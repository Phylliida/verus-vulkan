use vstd::prelude::*;

verus! {

use crate::allocator::*;
use crate::memory_aliasing::*;
use crate::resource::*;
use crate::runtime::memory_aliasing::*;
use crate::allocator_proofs::*;

//  ─── Spec functions ────────────────────────────────────────────

///  Convert an AllocationRecord to a MemoryRange for aliasing tracking.
pub open spec fn allocation_to_memory_range(alloc: AllocationRecord, block_id: nat) -> MemoryRange {
    MemoryRange {
        allocation_id: block_id,
        offset: alloc.offset,
        size: alloc.size,
    }
}

///  Whether an allocation is aligned to the given alignment.
pub open spec fn allocation_aligned_for_buffer(alloc: AllocationRecord, alignment: nat) -> bool
    recommends alignment > 0,
{
    alloc.offset % alignment == 0
}

///  Whether an allocation is large enough for a resource.
pub open spec fn allocation_fits_resource(alloc: AllocationRecord, required_size: nat) -> bool {
    alloc.size >= required_size
}

///  Combined validity: allocation is aligned, fits, and within block.
pub open spec fn binding_valid_for_resource(
    alloc: AllocationRecord,
    block_size: nat,
    required_size: nat,
    alignment: nat,
) -> bool {
    allocation_aligned_for_buffer(alloc, alignment)
    && allocation_fits_resource(alloc, required_size)
    && alloc_end(alloc) <= block_size
    && alloc.size > 0
}

///  Whether an allocation from this sub-allocator doesn't overlap any existing allocation's
///  memory range — i.e., it's safe to bind.
pub open spec fn allocator_binding_safe(sub: SubAllocatorState, alloc: AllocationRecord) -> bool {
    forall|id: nat|
        #![trigger sub.allocations[id]]
        sub.allocations.contains_key(id)
        ==> alloc_end(sub.allocations[id]) <= alloc.offset
            || alloc_end(alloc) <= sub.allocations[id].offset
}

//  ─── Proof functions ───────────────────────────────────────────

///  Helper: find_best_fit returning Some(idx) implies block_can_fit on that block.
proof fn lemma_find_best_fit_implies_can_fit(
    free_list: Seq<FreeBlock>,
    size: nat,
    alignment: nat,
)
    requires
        find_best_fit(free_list, size, alignment).is_some(),
    ensures
        ({
            let idx = find_best_fit(free_list, size, alignment).unwrap();
            idx < free_list.len()
            && block_can_fit(free_list[idx as int], size, alignment)
        }),
    decreases free_list.len(),
{
    if free_list.len() == 0 {
        //  Contradiction: find_best_fit returns None for empty list
    } else if block_can_fit(free_list[0], size, alignment) {
        //  find_best_fit returns Some(0), block_can_fit(free_list[0], ...)
    } else {
        let rest = free_list.subrange(1, free_list.len() as int);
        lemma_find_best_fit_implies_can_fit(rest, size, alignment);
        let j = find_best_fit(rest, size, alignment).unwrap();
        //  find_best_fit(free_list, ...) == Some(j + 1)
        //  block_can_fit(rest[j], ...) == block_can_fit(free_list[j+1], ...)
        assert(rest[j as int] == free_list[(j + 1) as int]);
    }
}

///  A successful allocation produces an aligned result.
pub proof fn lemma_allocate_produces_aligned(
    sub: SubAllocatorState,
    size: nat,
    alignment: nat,
)
    requires
        sub_allocator_well_formed(sub),
        alignment > 0,
        size > 0,
        allocate_from_block(sub, size, alignment).is_some(),
    ensures
        ({
            let (new_sub, alloc) = allocate_from_block(sub, size, alignment).unwrap();
            allocation_aligned_for_buffer(alloc, alignment)
        }),
{
    lemma_find_best_fit_implies_can_fit(sub.free_list, size, alignment);
    let idx = find_best_fit(sub.free_list, size, alignment).unwrap();
    let block = sub.free_list[idx as int];
    lemma_align_up_aligned(block.offset, alignment);
}

///  A successful allocation stays within the block.
pub proof fn lemma_allocate_within_bounds(
    sub: SubAllocatorState,
    size: nat,
    alignment: nat,
)
    requires
        sub_allocator_well_formed(sub),
        alignment > 0,
        size > 0,
        allocate_from_block(sub, size, alignment).is_some(),
    ensures
        ({
            let (new_sub, alloc) = allocate_from_block(sub, size, alignment).unwrap();
            alloc_end(alloc) <= sub.block_size
            && alloc.size > 0
        }),
{
    lemma_find_best_fit_implies_can_fit(sub.free_list, size, alignment);
    let idx = find_best_fit(sub.free_list, size, alignment).unwrap();
    let block = sub.free_list[idx as int];
    lemma_alignment_within_block(block, size, alignment);
    //  free_list_within_bounds from wf: free_block_end(block) <= block_size
    //  Trigger: free_list[idx as int]
    assert(free_block_end(sub.free_list[idx as int]) <= sub.block_size);
}

///  A successful allocation does not overlap any existing allocation.
pub proof fn lemma_allocate_no_overlap_existing(
    sub: SubAllocatorState,
    size: nat,
    alignment: nat,
)
    requires
        sub_allocator_well_formed(sub),
        alignment > 0,
        size > 0,
        allocate_from_block(sub, size, alignment).is_some(),
    ensures
        ({
            let (new_sub, alloc) = allocate_from_block(sub, size, alignment).unwrap();
            allocator_binding_safe(sub, alloc)
        }),
{
    lemma_find_best_fit_implies_can_fit(sub.free_list, size, alignment);
    let idx = find_best_fit(sub.free_list, size, alignment).unwrap();
    let block = sub.free_list[idx as int];
    lemma_alignment_within_block(block, size, alignment);

    let (new_sub, alloc) = allocate_from_block(sub, size, alignment).unwrap();

    //  alloc.offset = align_up(block.offset, alignment) >= block.offset
    //  alloc_end(alloc) = alloc.offset + size <= free_block_end(block)
    //  no_overlap_alloc_free: for all alloc id and free block fi,
    //    alloc_end(allocs[id]) <= free_list[fi].offset || free_block_end(free_list[fi]) <= allocs[id].offset
    assert(no_overlap_alloc_free(sub.allocations, sub.free_list));

    assert forall|id: nat|
        #![trigger sub.allocations[id]]
        sub.allocations.contains_key(id)
    implies
        alloc_end(sub.allocations[id]) <= alloc.offset
        || alloc_end(alloc) <= sub.allocations[id].offset
    by {
        let existing = sub.allocations[id];
        //  Trigger no_overlap_alloc_free with (id, idx)
        assert(sub.allocations.contains_key(id) && idx < sub.free_list.len());
        //  This gives us: alloc_end(existing) <= block.offset || free_block_end(block) <= existing.offset
        assert(alloc_end(existing) <= sub.free_list[idx as int].offset
            || free_block_end(sub.free_list[idx as int]) <= existing.offset);
        //  alloc.offset >= block.offset and alloc_end(alloc) <= free_block_end(block)
    }
}

///  Non-overlapping allocations produce non-overlapping memory ranges.
pub proof fn lemma_allocation_to_range_no_overlap(
    a1: AllocationRecord,
    a2: AllocationRecord,
    block_id: nat,
)
    requires
        alloc_end(a1) <= a2.offset || alloc_end(a2) <= a1.offset,
    ensures
        ranges_disjoint(
            allocation_to_memory_range(a1, block_id),
            allocation_to_memory_range(a2, block_id),
        ),
{
    let r1 = allocation_to_memory_range(a1, block_id);
    let r2 = allocation_to_memory_range(a2, block_id);
    //  r1 and r2 have the same allocation_id (block_id),
    //  but their byte ranges don't intersect
    assert(r1.offset + r1.size <= r2.offset || r2.offset + r2.size <= r1.offset);
}

///  Different blocks are trivially disjoint (different allocation_ids).
pub proof fn lemma_different_blocks_no_overlap(
    a1: AllocationRecord,
    a2: AllocationRecord,
    bid1: nat,
    bid2: nat,
)
    requires
        bid1 != bid2,
    ensures
        ranges_disjoint(
            allocation_to_memory_range(a1, bid1),
            allocation_to_memory_range(a2, bid2),
        ),
{
    let r1 = allocation_to_memory_range(a1, bid1);
    let r2 = allocation_to_memory_range(a2, bid2);
    assert(r1.allocation_id != r2.allocation_id);
}

///  **Crown jewel**: A well-formed allocator producing a successful allocation yields
///  a valid, non-overlapping memory range binding.
pub proof fn lemma_allocate_and_bind_safe(
    sub: SubAllocatorState,
    size: nat,
    alignment: nat,
    block_id: nat,
)
    requires
        sub_allocator_well_formed(sub),
        alignment > 0,
        size > 0,
        allocate_from_block(sub, size, alignment).is_some(),
    ensures
        ({
            let (new_sub, alloc) = allocate_from_block(sub, size, alignment).unwrap();
            let range = allocation_to_memory_range(alloc, block_id);
            binding_valid_for_resource(alloc, sub.block_size, size, alignment)
            && allocator_binding_safe(sub, alloc)
            && range.size > 0
        }),
{
    lemma_allocate_produces_aligned(sub, size, alignment);
    lemma_allocate_within_bounds(sub, size, alignment);
    lemma_allocate_no_overlap_existing(sub, size, alignment);
    let (new_sub, alloc) = allocate_from_block(sub, size, alignment).unwrap();
    assert(alloc.size >= size);
}

///  After freeing an allocation, its range is available for reuse (no longer in allocations map).
pub proof fn lemma_free_enables_rebind(
    sub: SubAllocatorState,
    alloc_id: nat,
)
    requires
        sub_allocator_well_formed(sub),
        sub.allocations.contains_key(alloc_id),
    ensures
        ({
            let new_sub = free_allocation(sub, alloc_id);
            !new_sub.allocations.contains_key(alloc_id)
        }),
{
    //  Directly from free_allocation definition: allocations.remove(alloc_id)
}

///  All allocations in a well-formed sub-allocator produce pairwise non-overlapping MemoryRanges.
pub proof fn lemma_wf_allocator_all_bindings_safe(
    sub: SubAllocatorState,
    block_id: nat,
)
    requires
        sub_allocator_well_formed(sub),
    ensures
        forall|id1: nat, id2: nat|
            #![trigger sub.allocations[id1], sub.allocations[id2]]
            sub.allocations.contains_key(id1)
            && sub.allocations.contains_key(id2)
            && id1 != id2
            ==> ranges_disjoint(
                allocation_to_memory_range(sub.allocations[id1], block_id),
                allocation_to_memory_range(sub.allocations[id2], block_id),
            ),
{
    assert(allocations_non_overlapping(sub.allocations));
    assert forall|id1: nat, id2: nat|
        #![trigger sub.allocations[id1], sub.allocations[id2]]
        sub.allocations.contains_key(id1)
        && sub.allocations.contains_key(id2)
        && id1 != id2
    implies
        ranges_disjoint(
            allocation_to_memory_range(sub.allocations[id1], block_id),
            allocation_to_memory_range(sub.allocations[id2], block_id),
        )
    by {
        let a1 = sub.allocations[id1];
        let a2 = sub.allocations[id2];
        assert(alloc_end(a1) <= a2.offset || alloc_end(a2) <= a1.offset);
        lemma_allocation_to_range_no_overlap(a1, a2, block_id);
    }
}

//  ─── Exec functions ────────────────────────────────────────────

///  Exec: allocate from a sub-allocator and bind the resulting range to a resource in the tracker.
pub fn allocate_and_bind_exec(
    sub: Ghost<SubAllocatorState>,
    tracker: &mut RuntimeAliasingTracker,
    resource: Ghost<ResourceId>,
    size: Ghost<nat>,
    alignment: Ghost<nat>,
    block_id: Ghost<nat>,
)
    requires
        sub_allocator_well_formed(sub@),
        alignment@ > 0,
        size@ > 0,
        allocate_from_block(sub@, size@, alignment@).is_some(),
        !old(tracker).in_flight@.contains(resource@),
        !old(tracker).bindings@.contains_key(resource@),
    ensures
        ({
            let (new_sub, alloc) = allocate_from_block(sub@, size@, alignment@).unwrap();
            let range = allocation_to_memory_range(alloc, block_id@);
            tracker.bindings@ == old(tracker).bindings@.insert(resource@, range)
            && tracker.in_flight@ == old(tracker).in_flight@
            && binding_valid_for_resource(alloc, sub@.block_size, size@, alignment@)
        }),
{
    proof {
        lemma_allocate_and_bind_safe(sub@, size@, alignment@, block_id@);
    }
    let ghost (new_sub, alloc) = allocate_from_block(sub@, size@, alignment@).unwrap();
    let ghost range = allocation_to_memory_range(alloc, block_id@);
    bind_resource_exec(tracker, resource, Ghost(range));
}

///  Exec: free an allocation and unbind the corresponding resource from the tracker.
pub fn free_and_unbind_exec(
    sub: Ghost<SubAllocatorState>,
    tracker: &mut RuntimeAliasingTracker,
    alloc_id: Ghost<nat>,
    resource: Ghost<ResourceId>,
)
    requires
        sub_allocator_well_formed(sub@),
        sub@.allocations.contains_key(alloc_id@),
        !old(tracker).in_flight@.contains(resource@),
        old(tracker).bindings@.contains_key(resource@),
    ensures
        ({
            let new_sub = free_allocation(sub@, alloc_id@);
            !new_sub.allocations.contains_key(alloc_id@)
            && tracker.bindings@ == old(tracker).bindings@.remove(resource@)
            && tracker.in_flight@ == old(tracker).in_flight@
        }),
{
    proof {
        lemma_free_enables_rebind(sub@, alloc_id@);
    }
    unbind_resource_exec(tracker, resource);
}

} //  verus!
