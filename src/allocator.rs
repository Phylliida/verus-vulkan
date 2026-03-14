use vstd::prelude::*;

verus! {

// ── Types ──────────────────────────────────────────────────────────────

/// Allocation strategy for a sub-allocator.
pub enum AllocationStrategy {
    /// Linear (bump) allocation.
    Linear,
    /// Power-of-2 buddy system.
    BuddySystem,
    /// Fixed-size slab allocation.
    Slab { slab_size: nat },
}

/// A contiguous free region within a memory block.
pub struct FreeBlock {
    pub offset: nat,
    pub size: nat,
}

/// A live allocation record.
pub struct AllocationRecord {
    pub id: nat,
    pub offset: nat,
    pub size: nat,
    pub memory_type: nat,
    pub generation: nat,
}

/// Ghost state for a sub-allocator managing a single memory block.
pub struct SubAllocatorState {
    /// ID of the underlying VkDeviceMemory block.
    pub memory_block_id: nat,
    /// Total size of the memory block in bytes.
    pub block_size: nat,
    /// Strategy used by this sub-allocator.
    pub strategy: AllocationStrategy,
    /// Sorted list of free regions.
    pub free_list: Seq<FreeBlock>,
    /// Live allocations keyed by allocation ID.
    pub allocations: Map<nat, AllocationRecord>,
    /// Next allocation ID to issue.
    pub next_id: nat,
    /// Monotonically increasing generation counter.
    pub generation: nat,
    /// Running total of allocated bytes.
    pub total_alloc_size: nat,
}

/// Ghost state for the top-level allocator managing multiple memory blocks.
pub struct AllocatorState {
    /// Sub-allocators, one per memory block.
    pub sub_allocators: Seq<SubAllocatorState>,
    /// Memory type indices for each sub-allocator.
    pub memory_types: Seq<nat>,
    /// Total bytes allocated across all sub-allocators.
    pub total_allocated: nat,
    /// Global allocation budget limit.
    pub budget_limit: nat,
    /// False after the allocator is destroyed.
    pub alive: bool,
}

// ── Helper Specs ──────────────────────────────────────────────────────

/// End offset of a free block.
pub open spec fn free_block_end(block: FreeBlock) -> nat {
    block.offset + block.size
}

/// End offset of an allocation.
pub open spec fn alloc_end(alloc: AllocationRecord) -> nat {
    alloc.offset + alloc.size
}

/// Round up `offset` to the next multiple of `alignment`.
pub open spec fn align_up(offset: nat, alignment: nat) -> nat
    recommends alignment > 0,
{
    if alignment == 0 { offset }
    else if offset % alignment == 0 { offset }
    else { (offset + alignment - offset % alignment) as nat }
}

/// True iff `offset` is a multiple of `alignment`.
pub open spec fn is_aligned(offset: nat, alignment: nat) -> bool {
    alignment > 0 && offset % alignment == 0
}

/// Sum of sizes in a free list.
pub open spec fn free_list_total_size(free_list: Seq<FreeBlock>) -> nat
    decreases free_list.len(),
{
    if free_list.len() == 0 {
        0
    } else {
        free_list[0].size + free_list_total_size(free_list.subrange(1, free_list.len() as int))
    }
}

/// Size of the largest free block.
pub open spec fn largest_free_block(free_list: Seq<FreeBlock>) -> nat
    decreases free_list.len(),
{
    if free_list.len() == 0 {
        0
    } else {
        let rest_max = largest_free_block(free_list.subrange(1, free_list.len() as int));
        if free_list[0].size >= rest_max { free_list[0].size }
        else { rest_max }
    }
}

/// True iff `n` is a power of 2.
pub open spec fn is_power_of_two(n: nat) -> bool
    decreases n,
{
    n == 1 || (n > 1 && n % 2 == 0 && is_power_of_two(n / 2))
}

/// Smallest power of 2 >= size.
pub open spec fn buddy_round_up(size: nat) -> nat
    recommends size > 0,
    decreases size,
{
    if size <= 1 { 1 }
    else { 2 * buddy_round_up((size + 1) / 2) }
}

/// Insert a free block into a sorted free list maintaining offset order.
pub open spec fn insert_free_block_sorted(
    free_list: Seq<FreeBlock>, block: FreeBlock,
) -> Seq<FreeBlock>
    decreases free_list.len(),
{
    if free_list.len() == 0 {
        seq![block]
    } else if block.offset <= free_list[0].offset {
        seq![block] + free_list
    } else {
        seq![free_list[0]] + insert_free_block_sorted(
            free_list.subrange(1, free_list.len() as int), block,
        )
    }
}

// ── Well-Formedness Specs ────────────────────────────────────────────

/// Free list is sorted by offset (strictly increasing).
pub open spec fn free_list_sorted(free_list: Seq<FreeBlock>) -> bool {
    forall|i: nat|
        #![trigger free_list[i as int]]
        i + 1 < free_list.len()
        ==> free_list[i as int].offset < free_list[(i + 1) as int].offset
}

/// Free list blocks are non-overlapping.
pub open spec fn free_list_non_overlapping(free_list: Seq<FreeBlock>) -> bool {
    forall|i: nat|
        #![trigger free_list[i as int]]
        i + 1 < free_list.len()
        ==> free_block_end(free_list[i as int]) <= free_list[(i + 1) as int].offset
}

/// All free blocks lie within [0, block_size).
pub open spec fn free_list_within_bounds(free_list: Seq<FreeBlock>, block_size: nat) -> bool {
    forall|i: nat|
        #![trigger free_list[i as int]]
        i < free_list.len()
        ==> free_block_end(free_list[i as int]) <= block_size
}

/// All free blocks have positive size.
pub open spec fn free_list_positive_sizes(free_list: Seq<FreeBlock>) -> bool {
    forall|i: nat|
        #![trigger free_list[i as int]]
        i < free_list.len() ==> free_list[i as int].size > 0
}

/// The free list is well-formed for the given block size.
pub open spec fn free_list_well_formed(free_list: Seq<FreeBlock>, block_size: nat) -> bool {
    free_list_sorted(free_list)
    && free_list_non_overlapping(free_list)
    && free_list_within_bounds(free_list, block_size)
    && free_list_positive_sizes(free_list)
}

/// All allocations lie within [0, block_size) and have positive size.
pub open spec fn allocations_within_bounds(
    allocs: Map<nat, AllocationRecord>, block_size: nat,
) -> bool {
    forall|id: nat|
        #![trigger allocs[id]]
        allocs.contains_key(id)
        ==> alloc_end(allocs[id]) <= block_size && allocs[id].size > 0
}

/// No two allocations overlap.
pub open spec fn allocations_non_overlapping(allocs: Map<nat, AllocationRecord>) -> bool {
    forall|id1: nat, id2: nat|
        #![trigger allocs[id1], allocs[id2]]
        allocs.contains_key(id1) && allocs.contains_key(id2) && id1 != id2
        ==> alloc_end(allocs[id1]) <= allocs[id2].offset
            || alloc_end(allocs[id2]) <= allocs[id1].offset
}

/// Allocations are well-formed for the given block size.
pub open spec fn allocations_well_formed(
    allocs: Map<nat, AllocationRecord>, block_size: nat,
) -> bool {
    allocations_within_bounds(allocs, block_size)
    && allocations_non_overlapping(allocs)
}

/// No allocation overlaps any free block.
pub open spec fn no_overlap_alloc_free(
    allocs: Map<nat, AllocationRecord>,
    free_list: Seq<FreeBlock>,
) -> bool {
    forall|id: nat, fi: nat|
        #![trigger allocs[id], free_list[fi as int]]
        allocs.contains_key(id) && fi < free_list.len()
        ==> alloc_end(allocs[id]) <= free_list[fi as int].offset
            || free_block_end(free_list[fi as int]) <= allocs[id].offset
}

/// Total allocated + total free = block size.
pub open spec fn total_coverage(
    total_alloc_size: nat,
    free_list: Seq<FreeBlock>,
    block_size: nat,
) -> bool {
    total_alloc_size + free_list_total_size(free_list) == block_size
}

/// All allocation IDs are less than next_id.
pub open spec fn all_ids_below_next(
    allocs: Map<nat, AllocationRecord>, next_id: nat,
) -> bool {
    forall|id: nat|
        #![trigger allocs[id]]
        allocs.contains_key(id) ==> id < next_id
}

/// A sub-allocator is well-formed.
pub open spec fn sub_allocator_well_formed(sub: SubAllocatorState) -> bool {
    free_list_well_formed(sub.free_list, sub.block_size)
    && allocations_well_formed(sub.allocations, sub.block_size)
    && no_overlap_alloc_free(sub.allocations, sub.free_list)
    && total_coverage(sub.total_alloc_size, sub.free_list, sub.block_size)
    && all_ids_below_next(sub.allocations, sub.next_id)
    && sub.block_size > 0
}

/// The top-level allocator is well-formed.
pub open spec fn allocator_well_formed(alloc: AllocatorState) -> bool {
    alloc.alive
    && alloc.memory_types.len() == alloc.sub_allocators.len()
    && (forall|i: nat|
        #![trigger alloc.sub_allocators[i as int]]
        i < alloc.sub_allocators.len()
        ==> sub_allocator_well_formed(alloc.sub_allocators[i as int]))
    && within_budget(alloc)
}

// ── Allocation Specs ────────────────────────────────────────────────

/// True iff a free block can accommodate an aligned allocation of `size`.
pub open spec fn block_can_fit(block: FreeBlock, size: nat, alignment: nat) -> bool {
    alignment > 0
    && size > 0
    && align_up(block.offset, alignment) + size <= free_block_end(block)
}

/// True iff there exists a free block that can fit the request.
pub open spec fn can_allocate(sub: SubAllocatorState, size: nat, alignment: nat) -> bool {
    exists|i: nat|
        #![trigger sub.free_list[i as int]]
        i < sub.free_list.len()
        && block_can_fit(sub.free_list[i as int], size, alignment)
}

/// Find the first free block that fits (first-fit strategy).
pub open spec fn find_best_fit(
    free_list: Seq<FreeBlock>, size: nat, alignment: nat,
) -> Option<nat>
    decreases free_list.len(),
{
    if free_list.len() == 0 {
        None
    } else if block_can_fit(free_list[0], size, alignment) {
        Some(0nat)
    } else {
        match find_best_fit(
            free_list.subrange(1, free_list.len() as int), size, alignment,
        ) {
            Some(j) => Some(j + 1),
            None => None,
        }
    }
}

/// Create an allocation at free block `block_idx`, splitting it as needed.
pub open spec fn allocate_at(
    sub: SubAllocatorState, block_idx: nat, size: nat, alignment: nat,
) -> (SubAllocatorState, AllocationRecord)
    recommends
        block_idx < sub.free_list.len(),
        block_can_fit(sub.free_list[block_idx as int], size, alignment),
{
    let block = sub.free_list[block_idx as int];
    let aligned_offset = align_up(block.offset, alignment);
    let alloc = AllocationRecord {
        id: sub.next_id,
        offset: aligned_offset,
        size: size,
        memory_type: 0,
        generation: sub.generation,
    };
    let prefix = if aligned_offset > block.offset {
        seq![FreeBlock {
            offset: block.offset,
            size: (aligned_offset - block.offset) as nat,
        }]
    } else {
        Seq::<FreeBlock>::empty()
    };
    let suffix = if aligned_offset + size < free_block_end(block) {
        seq![FreeBlock {
            offset: aligned_offset + size,
            size: (free_block_end(block) - aligned_offset - size) as nat,
        }]
    } else {
        Seq::<FreeBlock>::empty()
    };
    let new_free_list =
        sub.free_list.subrange(0, block_idx as int)
        + prefix + suffix
        + sub.free_list.subrange((block_idx + 1) as int, sub.free_list.len() as int);
    (SubAllocatorState {
        free_list: new_free_list,
        allocations: sub.allocations.insert(sub.next_id, alloc),
        next_id: sub.next_id + 1,
        total_alloc_size: sub.total_alloc_size + size,
        ..sub
    }, alloc)
}

/// Perform a first-fit allocation.
pub open spec fn allocate_from_block(
    sub: SubAllocatorState, size: nat, alignment: nat,
) -> Option<(SubAllocatorState, AllocationRecord)> {
    match find_best_fit(sub.free_list, size, alignment) {
        Some(idx) => Some(allocate_at(sub, idx, size, alignment)),
        None => None,
    }
}

/// Free an allocation by ID, returning its space to the sorted free list.
pub open spec fn free_allocation(
    sub: SubAllocatorState, alloc_id: nat,
) -> SubAllocatorState
    recommends sub.allocations.contains_key(alloc_id),
{
    let alloc = sub.allocations[alloc_id];
    SubAllocatorState {
        free_list: insert_free_block_sorted(
            sub.free_list,
            FreeBlock { offset: alloc.offset, size: alloc.size },
        ),
        allocations: sub.allocations.remove(alloc_id),
        total_alloc_size: (sub.total_alloc_size - alloc.size) as nat,
        ..sub
    }
}

/// Merge adjacent free blocks in a sorted free list.
pub open spec fn coalesce_free_list(free_list: Seq<FreeBlock>) -> Seq<FreeBlock>
    decreases free_list.len(),
{
    if free_list.len() <= 1 {
        free_list
    } else if free_block_end(free_list[0]) == free_list[1].offset {
        coalesce_free_list(
            seq![FreeBlock {
                offset: free_list[0].offset,
                size: free_list[0].size + free_list[1].size,
            }] + free_list.subrange(2, free_list.len() as int)
        )
    } else {
        seq![free_list[0]] + coalesce_free_list(
            free_list.subrange(1, free_list.len() as int),
        )
    }
}

/// Split a buddy block into two equal halves.
pub open spec fn buddy_split(block: FreeBlock) -> (FreeBlock, FreeBlock)
    recommends block.size >= 2,
{
    let half = block.size / 2;
    (
        FreeBlock { offset: block.offset, size: half },
        FreeBlock { offset: block.offset + half, size: half },
    )
}

/// Buddy-system allocation: round up size and allocate.
pub open spec fn buddy_allocate(
    sub: SubAllocatorState, size: nat, alignment: nat,
) -> Option<(SubAllocatorState, AllocationRecord)>
    recommends size > 0,
{
    allocate_from_block(sub, buddy_round_up(size), alignment)
}

/// Buddy-system free: free and coalesce.
pub open spec fn buddy_free(sub: SubAllocatorState, alloc_id: nat) -> SubAllocatorState
    recommends sub.allocations.contains_key(alloc_id),
{
    defragment_step(free_allocation(sub, alloc_id))
}

/// Compute external fragmentation: total free - largest free block.
pub open spec fn compute_fragmentation(sub: SubAllocatorState) -> nat {
    let total_free = free_list_total_size(sub.free_list);
    let largest = largest_free_block(sub.free_list);
    (total_free - largest) as nat
}

/// True iff the allocator is within its budget.
pub open spec fn within_budget(alloc: AllocatorState) -> bool {
    alloc.total_allocated <= alloc.budget_limit
}

/// Defragment by coalescing the free list.
pub open spec fn defragment_step(sub: SubAllocatorState) -> SubAllocatorState {
    SubAllocatorState {
        free_list: coalesce_free_list(sub.free_list),
        ..sub
    }
}

// ── Extended Specs ──────────────────────────────────────────────────

/// Free space in a sub-allocator.
pub open spec fn sub_allocator_free_space(sub: SubAllocatorState) -> nat {
    free_list_total_size(sub.free_list)
}

/// Utilization of a sub-allocator (allocated / block_size as ratio numerator).
pub open spec fn sub_allocator_utilization(sub: SubAllocatorState) -> nat {
    sub.total_alloc_size
}

/// Number of free blocks.
pub open spec fn free_block_count(sub: SubAllocatorState) -> nat {
    sub.free_list.len()
}

/// True iff the sub-allocator has no live allocations.
pub open spec fn is_empty_sub_allocator(sub: SubAllocatorState) -> bool {
    sub.total_alloc_size == 0
}

/// True iff two free blocks are adjacent (one ends where the other starts).
pub open spec fn blocks_adjacent(a: FreeBlock, b: FreeBlock) -> bool {
    free_block_end(a) == b.offset
}

/// True iff two free blocks can be merged.
pub open spec fn can_merge_blocks(a: FreeBlock, b: FreeBlock) -> bool {
    blocks_adjacent(a, b) || blocks_adjacent(b, a)
}

/// True iff the free list has no gaps (contiguous from first to last block).
pub open spec fn free_list_contiguous(free_list: Seq<FreeBlock>) -> bool {
    forall|i: nat|
        #![trigger free_list[i as int]]
        i + 1 < free_list.len()
        ==> free_block_end(free_list[i as int]) == free_list[(i + 1) as int].offset
}

/// True iff a slab sub-allocator can fit an allocation of the given size.
pub open spec fn slab_fits(sub: SubAllocatorState, size: nat) -> bool {
    match sub.strategy {
        AllocationStrategy::Slab { slab_size } => size <= slab_size && sub.free_list.len() > 0,
        _ => false,
    }
}

/// Ghost update: destroy the allocator.
pub open spec fn destroy_allocator(alloc: AllocatorState) -> AllocatorState {
    AllocatorState {
        alive: false,
        ..alloc
    }
}

/// Create a fresh sub-allocator with default state.
pub open spec fn create_sub_allocator(id: nat, size: nat, strategy: AllocationStrategy) -> SubAllocatorState {
    SubAllocatorState {
        memory_block_id: id,
        block_size: size,
        strategy: strategy,
        free_list: seq![FreeBlock { offset: 0, size: size }],
        allocations: Map::empty(),
        next_id: 0,
        generation: 0,
        total_alloc_size: 0,
    }
}

/// Number of free blocks after coalescing.
pub open spec fn coalesced_block_count(free_list: Seq<FreeBlock>) -> nat {
    coalesce_free_list(free_list).len()
}

/// Free list total covers the full block when fully free.
pub open spec fn fully_free(sub: SubAllocatorState) -> bool {
    sub.total_alloc_size == 0
    && free_list_total_size(sub.free_list) == sub.block_size
}

/// Fragmentation ratio: 0 means no fragmentation, higher means more.
pub open spec fn fragmentation_ratio(sub: SubAllocatorState) -> nat {
    if sub.free_list.len() == 0 { 0 }
    else { (sub.free_list.len() - 1) as nat }
}

/// Sub-allocator is fully allocated (no free space).
pub open spec fn fully_allocated(sub: SubAllocatorState) -> bool {
    sub.free_list.len() == 0
}

/// Sum of allocation sizes matches total_alloc_size (spec-level invariant).
pub open spec fn alloc_sizes_sum_correct(sub: SubAllocatorState) -> bool {
    sub.total_alloc_size + free_list_total_size(sub.free_list) == sub.block_size
}

// ── Safety Lemmas ────────────────────────────────────────────────────

/// Double-free is prevented: after freeing, the allocation is removed.
pub proof fn lemma_free_removes_allocation(sub: SubAllocatorState, alloc_id: nat)
    requires sub.allocations.contains_key(alloc_id),
    ensures !free_allocation(sub, alloc_id).allocations.contains_key(alloc_id),
{
}

} // verus!
