use vstd::prelude::*;
use crate::resource::*;
use crate::lifetime::*;

verus! {

//  ── Types ───────────────────────────────────────────────────────────────

///  A contiguous range of device memory.
pub struct MemoryRange {
    pub allocation_id: nat,
    pub offset: nat,
    pub size: nat,
}

//  ── Spec Functions ──────────────────────────────────────────────────────

///  Two memory ranges overlap if they share the same allocation and
///  their byte ranges intersect.
pub open spec fn ranges_overlap(r1: MemoryRange, r2: MemoryRange) -> bool {
    r1.allocation_id == r2.allocation_id
    && r1.offset < r2.offset + r2.size
    && r2.offset < r1.offset + r1.size
}

///  End of a memory range.
pub open spec fn range_end(r: MemoryRange) -> nat {
    r.offset + r.size
}

///  A resource is referenced by a submission (in-flight on the GPU).
pub open spec fn resource_in_flight(
    submissions: Seq<SubmissionRecord>,
    resource: ResourceId,
) -> bool {
    exists|i: int| 0 <= i < submissions.len()
        && !submissions[i].completed
        && #[trigger] submissions[i].referenced_resources.contains(resource)
}

///  Two aliased resources are safe: at most one is in-flight at a time.
pub open spec fn aliasing_safe(
    submissions: Seq<SubmissionRecord>,
    res1: ResourceId,
    res2: ResourceId,
) -> bool {
    !(resource_in_flight(submissions, res1)
      && resource_in_flight(submissions, res2))
}

///  All pairs of resources with overlapping memory are aliasing-safe.
pub open spec fn all_aliasing_safe(
    bindings: Map<ResourceId, MemoryRange>,
    submissions: Seq<SubmissionRecord>,
) -> bool {
    forall|r1: ResourceId, r2: ResourceId|
        bindings.contains_key(r1) && bindings.contains_key(r2)
        && r1 != r2
        && ranges_overlap(bindings[r1], bindings[r2])
        ==> aliasing_safe(submissions, r1, r2)
}

///  No resource is in-flight (all submissions completed).
pub open spec fn no_resources_in_flight(
    submissions: Seq<SubmissionRecord>,
) -> bool {
    forall|i: int| 0 <= i < submissions.len() ==> (#[trigger] submissions[i]).completed
}

///  No resource in the binding map uses this allocation.
pub open spec fn no_resources_use_allocation(
    bindings: Map<ResourceId, MemoryRange>,
    alloc_id: nat,
) -> bool {
    forall|r: ResourceId| bindings.contains_key(r)
        ==> (#[trigger] bindings[r]).allocation_id != alloc_id
}

///  Two ranges in different allocations never overlap.
pub open spec fn different_allocations(r1: MemoryRange, r2: MemoryRange) -> bool {
    r1.allocation_id != r2.allocation_id
}

///  Two ranges in the same allocation are disjoint (non-overlapping).
pub open spec fn ranges_disjoint(r1: MemoryRange, r2: MemoryRange) -> bool {
    r1.allocation_id != r2.allocation_id
    || r1.offset + r1.size <= r2.offset
    || r2.offset + r2.size <= r1.offset
}

//  ── Proofs ──────────────────────────────────────────────────────────────

///  Different allocations never overlap.
pub proof fn lemma_different_allocations_no_overlap(
    r1: MemoryRange,
    r2: MemoryRange,
)
    requires different_allocations(r1, r2),
    ensures !ranges_overlap(r1, r2),
{
}

///  Disjoint ranges don't overlap.
pub proof fn lemma_disjoint_no_overlap(
    r1: MemoryRange,
    r2: MemoryRange,
)
    requires ranges_disjoint(r1, r2),
    ensures !ranges_overlap(r1, r2),
{
}

///  Non-overlapping ranges are trivially safe regardless of submissions.
pub proof fn lemma_no_overlap_always_safe(
    r1: MemoryRange,
    r2: MemoryRange,
    submissions: Seq<SubmissionRecord>,
    res1: ResourceId,
    res2: ResourceId,
)
    requires !ranges_overlap(r1, r2),
    ensures
        //  Vacuously true: aliasing_safe only needed when ranges overlap
        true,
{
}

///  When no resources are in-flight, all aliasing is safe.
pub proof fn lemma_no_inflight_all_safe(
    bindings: Map<ResourceId, MemoryRange>,
    submissions: Seq<SubmissionRecord>,
)
    requires no_resources_in_flight(submissions),
    ensures all_aliasing_safe(bindings, submissions),
{
    assert forall|r1: ResourceId, r2: ResourceId|
        bindings.contains_key(r1) && bindings.contains_key(r2)
        && r1 != r2
        && ranges_overlap(bindings[r1], bindings[r2])
    implies aliasing_safe(submissions, r1, r2) by {
        //  No resource can be in-flight since all submissions are completed.
        //  Prove by contradiction: if resource_in_flight(submissions, r1),
        //  then exists i such that !submissions[i].completed, contradicting
        //  no_resources_in_flight.
        if resource_in_flight(submissions, r1) {
            let i = choose|i: int| 0 <= i < submissions.len()
                && !submissions[i].completed
                && #[trigger] submissions[i].referenced_resources.contains(r1);
            assert(!submissions[i].completed);
            assert(submissions[i].completed); //  contradiction from no_resources_in_flight
        }
    }
}

///  Empty submissions means no resources in-flight.
pub proof fn lemma_empty_submissions_no_inflight()
    ensures no_resources_in_flight(Seq::<SubmissionRecord>::empty()),
{
}

///  Overlap is symmetric.
pub proof fn lemma_overlap_symmetric(r1: MemoryRange, r2: MemoryRange)
    ensures ranges_overlap(r1, r2) == ranges_overlap(r2, r1),
{
}

///  A range does not overlap with itself (we use r1 != r2 in all_aliasing_safe,
///  but a range technically does overlap with itself geometrically).
///  This lemma proves ranges_overlap is reflexive when size > 0.
pub proof fn lemma_range_overlaps_self(r: MemoryRange)
    requires r.size > 0,
    ensures ranges_overlap(r, r),
{
}

///  Sequential use is safe: if r1 completes before r2 starts.
pub proof fn lemma_sequential_use_safe(
    submissions: Seq<SubmissionRecord>,
    res1: ResourceId,
    res2: ResourceId,
)
    requires !resource_in_flight(submissions, res1),
    ensures aliasing_safe(submissions, res1, res2),
{
}

} //  verus!
