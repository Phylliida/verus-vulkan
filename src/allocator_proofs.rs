use vstd::prelude::*;
use crate::allocator::*;

verus! {

//  ── Alignment Proofs ────────────────────────────────────────────────

///  align_up(offset, alignment) >= offset.
pub proof fn lemma_align_up_geq(offset: nat, alignment: nat)
    requires alignment > 0,
    ensures align_up(offset, alignment) >= offset,
{
    if offset % alignment == 0 {
    } else {
        assert(alignment > offset % alignment);
    }
}

///  align_up produces an aligned result.
pub proof fn lemma_align_up_aligned(offset: nat, alignment: nat)
    requires alignment > 0,
    ensures align_up(offset, alignment) % alignment == 0,
{
    if offset % alignment == 0 {
    } else {
        let r = offset % alignment;
        let result = offset + alignment - r;
        assert((result as int) % (alignment as int) == 0) by(nonlinear_arith)
            requires
                r == offset % alignment,
                0 < r,
                r < alignment,
                result == offset + alignment - r,
                alignment > 0,
        ;
    }
}

///  Aligned offset is still within the block when block_can_fit holds.
pub proof fn lemma_alignment_within_block(
    block: FreeBlock, size: nat, alignment: nat,
)
    requires block_can_fit(block, size, alignment),
    ensures
        align_up(block.offset, alignment) >= block.offset,
        align_up(block.offset, alignment) + size <= free_block_end(block),
{
    lemma_align_up_geq(block.offset, alignment);
}

//  ── Allocation Property Proofs ──────────────────────────────────────

///  Allocation increases total_alloc_size by exactly `size`.
pub proof fn lemma_allocate_increases_total(
    sub: SubAllocatorState,
    block_idx: nat,
    size: nat,
    alignment: nat,
)
    requires
        block_idx < sub.free_list.len(),
        block_can_fit(sub.free_list[block_idx as int], size, alignment),
    ensures ({
        let (new_sub, _) = allocate_at(sub, block_idx, size, alignment);
        new_sub.total_alloc_size == sub.total_alloc_size + size
    }),
{
}

///  Freeing decreases total_alloc_size by the allocation's size.
pub proof fn lemma_free_decreases_total(
    sub: SubAllocatorState,
    alloc_id: nat,
)
    requires
        sub.allocations.contains_key(alloc_id),
        sub.total_alloc_size >= sub.allocations[alloc_id].size,
    ensures
        free_allocation(sub, alloc_id).total_alloc_size
            == (sub.total_alloc_size - sub.allocations[alloc_id].size) as nat,
{
}

///  Allocating then freeing the same ID restores total_alloc_size.
pub proof fn lemma_allocate_free_roundtrip(
    sub: SubAllocatorState,
    block_idx: nat,
    size: nat,
    alignment: nat,
)
    requires
        block_idx < sub.free_list.len(),
        block_can_fit(sub.free_list[block_idx as int], size, alignment),
        !sub.allocations.contains_key(sub.next_id),
    ensures ({
        let (new_sub, alloc) = allocate_at(sub, block_idx, size, alignment);
        free_allocation(new_sub, alloc.id).total_alloc_size == sub.total_alloc_size
    }),
{
    let (new_sub, alloc) = allocate_at(sub, block_idx, size, alignment);
    assert(alloc.id == sub.next_id);
    assert(new_sub.allocations.contains_key(alloc.id));
    assert(new_sub.allocations[alloc.id].size == size);
    assert(new_sub.total_alloc_size == sub.total_alloc_size + size);
}

//  ── ID and Generation Proofs ────────────────────────────────────────

///  After freeing, the allocation ID is removed from the map.
pub proof fn lemma_no_double_free(
    sub: SubAllocatorState,
    alloc_id: nat,
)
    requires sub.allocations.contains_key(alloc_id),
    ensures !free_allocation(sub, alloc_id).allocations.contains_key(alloc_id),
{
}

///  The new allocation receives sub.next_id as its ID.
pub proof fn lemma_allocation_gets_next_id(
    sub: SubAllocatorState,
    block_idx: nat,
    size: nat,
    alignment: nat,
)
    requires
        block_idx < sub.free_list.len(),
        block_can_fit(sub.free_list[block_idx as int], size, alignment),
    ensures ({
        let (_, alloc) = allocate_at(sub, block_idx, size, alignment);
        alloc.id == sub.next_id
    }),
{
}

///  next_id increases by 1 after allocation.
pub proof fn lemma_next_id_increases(
    sub: SubAllocatorState,
    block_idx: nat,
    size: nat,
    alignment: nat,
)
    requires
        block_idx < sub.free_list.len(),
        block_can_fit(sub.free_list[block_idx as int], size, alignment),
    ensures ({
        let (new_sub, _) = allocate_at(sub, block_idx, size, alignment);
        new_sub.next_id == sub.next_id + 1
    }),
{
}

///  Generation is preserved during allocation.
pub proof fn lemma_generation_preserved(
    sub: SubAllocatorState,
    block_idx: nat,
    size: nat,
    alignment: nat,
)
    requires
        block_idx < sub.free_list.len(),
        block_can_fit(sub.free_list[block_idx as int], size, alignment),
    ensures ({
        let (new_sub, _) = allocate_at(sub, block_idx, size, alignment);
        new_sub.generation == sub.generation
    }),
{
}

//  ── Defragmentation Proofs ──────────────────────────────────────────

///  Defragmentation does not change the allocations map or related fields.
pub proof fn lemma_defragment_preserves_allocations(sub: SubAllocatorState)
    ensures
        defragment_step(sub).allocations == sub.allocations,
        defragment_step(sub).total_alloc_size == sub.total_alloc_size,
        defragment_step(sub).next_id == sub.next_id,
        defragment_step(sub).generation == sub.generation,
        defragment_step(sub).block_size == sub.block_size,
{
}

//  ── Buddy System Proofs ─────────────────────────────────────────────

///  Buddy split produces two blocks whose sizes sum to the original
///  (for power-of-2 sized blocks).
pub proof fn lemma_buddy_split_preserves_total(block: FreeBlock)
    requires
        block.size >= 2,
        is_power_of_two(block.size),
    ensures ({
        let (a, b) = buddy_split(block);
        a.size + b.size == block.size
    }),
{
    //  Power-of-2 and >= 2 implies even
    assert(block.size % 2 == 0);
    let half = block.size / 2;
    assert(half + half == block.size) by(nonlinear_arith)
        requires block.size % 2 == 0, half == block.size / 2;
}

///  buddy_round_up(size) >= size.
pub proof fn lemma_buddy_round_up_geq(size: nat)
    requires size > 0,
    ensures buddy_round_up(size) >= size,
    decreases size,
{
    if size <= 1 {
    } else {
        let half: nat = ((size + 1) / 2) as nat;
        assert(half == (size + 1) / 2);
        assert((size as int + 1) / 2 > 0) by(nonlinear_arith)
            requires size >= 2nat;
        assert((size as int + 1) / 2 < size as int) by(nonlinear_arith)
            requires size >= 2nat;
        assert(half > 0);
        assert(half < size);
        lemma_buddy_round_up_geq(half);
        assert(buddy_round_up(size) == 2 * buddy_round_up(half));
        assert((2 * ((size as int + 1) / 2)) >= size as int) by(nonlinear_arith)
            requires size >= 2nat;
        assert(2 * half >= size);
    }
}

///  buddy_round_up always returns a power of 2.
pub proof fn lemma_buddy_round_up_power_of_two(size: nat)
    requires size > 0,
    ensures is_power_of_two(buddy_round_up(size)),
    decreases size,
{
    if size <= 1 {
        //  buddy_round_up(1) = 1, is_power_of_two(1) = true
    } else {
        let half: nat = ((size + 1) / 2) as nat;
        assert(half == (size + 1) / 2);
        assert((size as int + 1) / 2 > 0) by(nonlinear_arith)
            requires size >= 2nat;
        assert((size as int + 1) / 2 < size as int) by(nonlinear_arith)
            requires size >= 2nat;
        assert(half > 0);
        assert(half < size);
        lemma_buddy_round_up_power_of_two(half);
        let x = buddy_round_up(half);
        assert(is_power_of_two(x));
        assert(buddy_round_up(size) == 2 * x);

        lemma_buddy_round_up_geq(half);
        assert(x >= 1);

        //  Show is_power_of_two(2 * x): need 2*x > 1, (2*x) % 2 == 0, (2*x)/2 == x
        assert(2 * x > 1);
        assert(((2 * x) as int) % 2 == 0) by(nonlinear_arith)
            requires x >= 1nat;
        assert((2 * x) / 2 == x) by(nonlinear_arith)
            requires x >= 1nat;
    }
}

//  ── Free List Structural Proofs ─────────────────────────────────────

///  Coalescing preserves the total free size.
pub proof fn lemma_coalesce_preserves_total_size(free_list: Seq<FreeBlock>)
    ensures
        free_list_total_size(coalesce_free_list(free_list))
            == free_list_total_size(free_list),
    decreases free_list.len(),
{
    if free_list.len() <= 1 {
    } else if free_block_end(free_list[0]) == free_list[1].offset {
        //  Merge case: first two blocks are adjacent
        let merged = FreeBlock {
            offset: free_list[0].offset,
            size: free_list[0].size + free_list[1].size,
        };
        let rest = free_list.subrange(2, free_list.len() as int);
        let merged_list = seq![merged] + rest;

        //  IH: coalesce(merged_list) preserves total
        lemma_coalesce_preserves_total_size(merged_list);

        //  Unfold total(free_list) = fl[0].size + total(fl[1..])
        let tail = free_list.subrange(1, free_list.len() as int);
        assert(free_list_total_size(free_list) == free_list[0].size + free_list_total_size(tail));

        //  Unfold total(tail) = fl[1].size + total(fl[2..])
        let tail_tail = tail.subrange(1, tail.len() as int);
        assert(tail_tail =~= rest);
        assert(free_list_total_size(tail) == free_list[1].size + free_list_total_size(tail_tail));

        //  Unfold total(merged_list) = merged.size + total(rest)
        let ml_tail = merged_list.subrange(1, merged_list.len() as int);
        assert(ml_tail =~= rest);
        assert(free_list_total_size(merged_list)
            == merged.size + free_list_total_size(ml_tail));

        //  Chain: total(free_list) = fl[0] + fl[1] + total(rest) = merged + total(rest) = total(merged_list)
        assert(free_list_total_size(free_list)
            == free_list[0].size + free_list[1].size + free_list_total_size(rest));
        assert(merged.size == free_list[0].size + free_list[1].size);
    } else {
        //  Non-merge case
        let tail = free_list.subrange(1, free_list.len() as int);
        lemma_coalesce_preserves_total_size(tail);

        //  Unfold coalesce(free_list) = seq![fl[0]] + coalesce(tail)
        //  Unfold total(result) = fl[0].size + total(coalesce(tail))
        let result = seq![free_list[0]] + coalesce_free_list(tail);
        let result_tail = result.subrange(1, result.len() as int);
        assert(result_tail =~= coalesce_free_list(tail));
        assert(free_list_total_size(result)
            == free_list[0].size + free_list_total_size(result_tail));
        assert(free_list_total_size(free_list)
            == free_list[0].size + free_list_total_size(tail));
    }
}

///  The largest free block size is <= total free size.
pub proof fn lemma_largest_free_block_leq_total(free_list: Seq<FreeBlock>)
    ensures largest_free_block(free_list) <= free_list_total_size(free_list),
    decreases free_list.len(),
{
    if free_list.len() == 0 {
    } else {
        let tail = free_list.subrange(1, free_list.len() as int);
        lemma_largest_free_block_leq_total(tail);
    }
}

///  Well-formedness implies no overlap (direct decomposition).
pub proof fn lemma_well_formed_implies_no_overlap(sub: SubAllocatorState)
    requires sub_allocator_well_formed(sub),
    ensures no_overlap_alloc_free(sub.allocations, sub.free_list),
{
}

///  insert_free_block_sorted preserves total size (adds block.size).
pub proof fn lemma_insert_preserves_total_size(
    free_list: Seq<FreeBlock>, block: FreeBlock,
)
    ensures
        free_list_total_size(insert_free_block_sorted(free_list, block))
            == free_list_total_size(free_list) + block.size,
    decreases free_list.len(),
{
    if free_list.len() == 0 {
        //  insert returns seq![block]
        let result = insert_free_block_sorted(free_list, block);
        assert(result =~= seq![block]);
        let rt = result.subrange(1, result.len() as int);
        assert(rt =~= Seq::<FreeBlock>::empty());
        assert(free_list_total_size(result) == block.size + free_list_total_size(rt));
        assert(free_list_total_size(free_list) == 0);
    } else if block.offset <= free_list[0].offset {
        //  insert returns seq![block] + free_list
        let result = insert_free_block_sorted(free_list, block);
        assert(result =~= seq![block] + free_list);
        let rt = result.subrange(1, result.len() as int);
        assert(rt =~= free_list);
        assert(free_list_total_size(result) == block.size + free_list_total_size(rt));
    } else {
        let tail = free_list.subrange(1, free_list.len() as int);
        lemma_insert_preserves_total_size(tail, block);

        //  insert returns seq![fl[0]] + insert_sorted(tail, block)
        let inserted_tail = insert_free_block_sorted(tail, block);
        let result = insert_free_block_sorted(free_list, block);
        assert(result =~= seq![free_list[0]] + inserted_tail);
        let rr = result.subrange(1, result.len() as int);
        assert(rr =~= inserted_tail);
        assert(free_list_total_size(result)
            == free_list[0].size + free_list_total_size(rr));
        assert(free_list_total_size(free_list)
            == free_list[0].size + free_list_total_size(tail));
    }
}

//  ── Budget Proofs ───────────────────────────────────────────────────

///  Budget is maintained after allocating if remaining capacity suffices.
pub proof fn lemma_within_budget_after_allocate(
    alloc: AllocatorState,
    additional: nat,
)
    requires
        within_budget(alloc),
        alloc.total_allocated + additional <= alloc.budget_limit,
    ensures within_budget(AllocatorState {
        total_allocated: alloc.total_allocated + additional,
        ..alloc
    }),
{
}

//  ── Constructor Proof ───────────────────────────────────────────────

///  A fresh sub-allocator with a single free block covering the entire
///  memory region is well-formed.
pub proof fn lemma_empty_sub_allocator_well_formed(block_size: nat)
    requires block_size > 0,
    ensures sub_allocator_well_formed(SubAllocatorState {
        memory_block_id: 0,
        block_size: block_size,
        strategy: AllocationStrategy::Linear,
        free_list: seq![FreeBlock { offset: 0, size: block_size }],
        allocations: Map::empty(),
        next_id: 0,
        generation: 0,
        total_alloc_size: 0,
    }),
{
    let sub = SubAllocatorState {
        memory_block_id: 0,
        block_size: block_size,
        strategy: AllocationStrategy::Linear,
        free_list: seq![FreeBlock { offset: 0, size: block_size }],
        allocations: Map::empty(),
        next_id: 0,
        generation: 0,
        total_alloc_size: 0,
    };
    assert(free_list_sorted(sub.free_list));
    assert(free_list_non_overlapping(sub.free_list));
    assert(free_list_within_bounds(sub.free_list, block_size));
    assert(free_list_positive_sizes(sub.free_list));

    assert(allocations_within_bounds(sub.allocations, block_size));
    assert(allocations_non_overlapping(sub.allocations));

    assert(no_overlap_alloc_free(sub.allocations, sub.free_list));

    //  Coverage: 0 + total_free == block_size
    let tail = sub.free_list.subrange(1, 1);
    assert(tail =~= Seq::<FreeBlock>::empty());
    assert(free_list_total_size(sub.free_list) == block_size + free_list_total_size(tail));

    assert(all_ids_below_next(sub.allocations, 0));
}

//  ── Extended Proofs ──────────────────────────────────────────────────

///  Fragmentation is at most the free space.
pub proof fn lemma_fragmentation_leq_free_space(sub: SubAllocatorState)
    ensures compute_fragmentation(sub) <= free_list_total_size(sub.free_list),
{
    lemma_largest_free_block_leq_total(sub.free_list);
}

///  An empty free list has zero total size.
pub proof fn lemma_empty_free_list_zero(fl: Seq<FreeBlock>)
    requires fl.len() == 0,
    ensures free_list_total_size(fl) == 0,
{
}

///  A single-block free list has total size == block size.
pub proof fn lemma_single_block_total(block: FreeBlock)
    ensures free_list_total_size(seq![block]) == block.size,
{
    let fl = seq![block];
    let tail = fl.subrange(1, fl.len() as int);
    assert(tail =~= Seq::<FreeBlock>::empty());
    assert(free_list_total_size(fl) == block.size + free_list_total_size(tail));
}

///  Destroying an allocator sets alive to false.
pub proof fn lemma_destroy_allocator_not_alive(alloc: AllocatorState)
    ensures !destroy_allocator(alloc).alive,
{
}

///  Destroying an allocator preserves sub-allocators.
pub proof fn lemma_destroy_preserves_sub_allocators(alloc: AllocatorState)
    ensures destroy_allocator(alloc).sub_allocators == alloc.sub_allocators,
{
}

///  Destroying an allocator preserves total_allocated.
pub proof fn lemma_destroy_preserves_total(alloc: AllocatorState)
    ensures destroy_allocator(alloc).total_allocated == alloc.total_allocated,
{
}

///  A created sub-allocator has zero allocations.
pub proof fn lemma_create_sub_allocator_empty(id: nat, size: nat, strategy: AllocationStrategy)
    requires size > 0,
    ensures
        create_sub_allocator(id, size, strategy).total_alloc_size == 0,
        is_empty_sub_allocator(create_sub_allocator(id, size, strategy)),
{
}

///  A created sub-allocator is fully free.
pub proof fn lemma_create_sub_allocator_fully_free(id: nat, size: nat, strategy: AllocationStrategy)
    requires size > 0,
    ensures fully_free(create_sub_allocator(id, size, strategy)),
{
    let sub = create_sub_allocator(id, size, strategy);
    lemma_single_block_total(FreeBlock { offset: 0, size: size });
    assert(sub.free_list =~= seq![FreeBlock { offset: 0, size: size }]);
}

///  Well-formed sub-allocator has total coverage.
pub proof fn lemma_well_formed_total_coverage(sub: SubAllocatorState)
    requires sub_allocator_well_formed(sub),
    ensures alloc_sizes_sum_correct(sub),
{
}

///  A well-formed sub-allocator has positive block size.
pub proof fn lemma_well_formed_positive_block_size(sub: SubAllocatorState)
    requires sub_allocator_well_formed(sub),
    ensures sub.block_size > 0,
{
}

///  Fully allocated sub-allocator has zero free space.
pub proof fn lemma_fully_allocated_zero_free(sub: SubAllocatorState)
    requires fully_allocated(sub),
    ensures free_list_total_size(sub.free_list) == 0,
{
}

///  Free space is non-negative (trivial for nat).
pub proof fn lemma_free_space_non_negative(sub: SubAllocatorState)
    ensures sub_allocator_free_space(sub) >= 0,
{
}

///  Block count after coalescing is at most original count.
pub proof fn lemma_coalesce_non_increasing_count(free_list: Seq<FreeBlock>)
    ensures coalesced_block_count(free_list) <= free_list.len(),
    decreases free_list.len(),
{
    if free_list.len() <= 1 {
    } else if free_block_end(free_list[0]) == free_list[1].offset {
        let merged = FreeBlock {
            offset: free_list[0].offset,
            size: free_list[0].size + free_list[1].size,
        };
        let rest = free_list.subrange(2, free_list.len() as int);
        let merged_list = seq![merged] + rest;
        assert(merged_list.len() == rest.len() + 1);
        assert(merged_list.len() < free_list.len());
        lemma_coalesce_non_increasing_count(merged_list);
    } else {
        let tail = free_list.subrange(1, free_list.len() as int);
        lemma_coalesce_non_increasing_count(tail);
    }
}

///  Adjacent blocks can be merged.
pub proof fn lemma_adjacent_implies_mergeable(a: FreeBlock, b: FreeBlock)
    requires blocks_adjacent(a, b),
    ensures can_merge_blocks(a, b),
{
}

///  A well-formed allocator is alive.
pub proof fn lemma_well_formed_is_alive(alloc: AllocatorState)
    requires allocator_well_formed(alloc),
    ensures alloc.alive,
{
}

///  A destroyed allocator is not well-formed.
pub proof fn lemma_destroyed_not_well_formed(alloc: AllocatorState)
    ensures !allocator_well_formed(destroy_allocator(alloc)),
{
}

///  Allocation preserves block_size.
pub proof fn lemma_allocate_preserves_block_size(
    sub: SubAllocatorState,
    block_idx: nat,
    size: nat,
    alignment: nat,
)
    requires
        block_idx < sub.free_list.len(),
        block_can_fit(sub.free_list[block_idx as int], size, alignment),
    ensures ({
        let (new_sub, _) = allocate_at(sub, block_idx, size, alignment);
        new_sub.block_size == sub.block_size
    }),
{
}

///  Allocation preserves strategy.
pub proof fn lemma_allocate_preserves_strategy(
    sub: SubAllocatorState,
    block_idx: nat,
    size: nat,
    alignment: nat,
)
    requires
        block_idx < sub.free_list.len(),
        block_can_fit(sub.free_list[block_idx as int], size, alignment),
    ensures ({
        let (new_sub, _) = allocate_at(sub, block_idx, size, alignment);
        new_sub.strategy == sub.strategy
    }),
{
}

///  Freeing preserves block_size.
pub proof fn lemma_free_preserves_block_size(
    sub: SubAllocatorState,
    alloc_id: nat,
)
    requires sub.allocations.contains_key(alloc_id),
    ensures free_allocation(sub, alloc_id).block_size == sub.block_size,
{
}

///  Freeing preserves strategy.
pub proof fn lemma_free_preserves_strategy(
    sub: SubAllocatorState,
    alloc_id: nat,
)
    requires sub.allocations.contains_key(alloc_id),
    ensures free_allocation(sub, alloc_id).strategy == sub.strategy,
{
}

//  ── Final Proofs ────────────────────────────────────────────────────

///  Freeing preserves next_id.
pub proof fn lemma_free_preserves_next_id(
    sub: SubAllocatorState,
    alloc_id: nat,
)
    requires sub.allocations.contains_key(alloc_id),
    ensures free_allocation(sub, alloc_id).next_id == sub.next_id,
{
}

///  Freeing preserves generation.
pub proof fn lemma_free_preserves_generation(
    sub: SubAllocatorState,
    alloc_id: nat,
)
    requires sub.allocations.contains_key(alloc_id),
    ensures free_allocation(sub, alloc_id).generation == sub.generation,
{
}

///  Freeing preserves memory_block_id.
pub proof fn lemma_free_preserves_memory_block_id(
    sub: SubAllocatorState,
    alloc_id: nat,
)
    requires sub.allocations.contains_key(alloc_id),
    ensures free_allocation(sub, alloc_id).memory_block_id == sub.memory_block_id,
{
}

///  Allocation preserves memory_block_id.
pub proof fn lemma_allocate_preserves_memory_block_id(
    sub: SubAllocatorState,
    block_idx: nat,
    size: nat,
    alignment: nat,
)
    requires
        block_idx < sub.free_list.len(),
        block_can_fit(sub.free_list[block_idx as int], size, alignment),
    ensures ({
        let (new_sub, _) = allocate_at(sub, block_idx, size, alignment);
        new_sub.memory_block_id == sub.memory_block_id
    }),
{
}

///  The new allocation has the correct size.
pub proof fn lemma_allocation_correct_size(
    sub: SubAllocatorState,
    block_idx: nat,
    size: nat,
    alignment: nat,
)
    requires
        block_idx < sub.free_list.len(),
        block_can_fit(sub.free_list[block_idx as int], size, alignment),
    ensures ({
        let (_, alloc) = allocate_at(sub, block_idx, size, alignment);
        alloc.size == size
    }),
{
}

///  The new allocation has the current generation.
pub proof fn lemma_allocation_current_generation(
    sub: SubAllocatorState,
    block_idx: nat,
    size: nat,
    alignment: nat,
)
    requires
        block_idx < sub.free_list.len(),
        block_can_fit(sub.free_list[block_idx as int], size, alignment),
    ensures ({
        let (_, alloc) = allocate_at(sub, block_idx, size, alignment);
        alloc.generation == sub.generation
    }),
{
}

///  After allocation, the new ID is in the allocations map.
pub proof fn lemma_allocation_in_map(
    sub: SubAllocatorState,
    block_idx: nat,
    size: nat,
    alignment: nat,
)
    requires
        block_idx < sub.free_list.len(),
        block_can_fit(sub.free_list[block_idx as int], size, alignment),
    ensures ({
        let (new_sub, alloc) = allocate_at(sub, block_idx, size, alignment);
        new_sub.allocations.contains_key(alloc.id)
    }),
{
}

///  Defragmentation preserves memory_block_id.
pub proof fn lemma_defragment_preserves_memory_block_id(sub: SubAllocatorState)
    ensures defragment_step(sub).memory_block_id == sub.memory_block_id,
{
}

///  Defragmentation preserves strategy.
pub proof fn lemma_defragment_preserves_strategy(sub: SubAllocatorState)
    ensures defragment_step(sub).strategy == sub.strategy,
{
}

///  Largest free block of empty list is 0.
pub proof fn lemma_empty_largest_zero()
    ensures largest_free_block(Seq::empty()) == 0,
{
}

///  Empty free list total size is 0.
pub proof fn lemma_empty_free_list_total_zero()
    ensures free_list_total_size(Seq::empty()) == 0,
{
}

///  Fragmentation of empty free list is 0.
pub proof fn lemma_empty_fragmentation_zero()
    ensures compute_fragmentation(SubAllocatorState {
        memory_block_id: 0,
        block_size: 1,
        strategy: AllocationStrategy::Linear,
        free_list: Seq::empty(),
        allocations: Map::empty(),
        next_id: 0,
        generation: 0,
        total_alloc_size: 0,
    }) == 0,
{
}

} //  verus!
