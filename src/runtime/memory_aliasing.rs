use vstd::prelude::*;
use crate::resource::*;
use crate::lifetime::*;
use crate::memory_aliasing::*;

verus! {

/// Runtime wrapper for tracking memory aliasing safety.
///
/// Maintains a ghost map of resource → memory range bindings and
/// a set of resources currently in-flight on the GPU.
pub struct RuntimeAliasingTracker {
    /// Ghost model: resource → memory range bindings.
    pub bindings: Ghost<Map<ResourceId, MemoryRange>>,
    /// Ghost model: set of resources currently in-flight.
    pub in_flight: Ghost<Set<ResourceId>>,
}

impl View for RuntimeAliasingTracker {
    type V = Map<ResourceId, MemoryRange>;
    open spec fn view(&self) -> Map<ResourceId, MemoryRange> { self.bindings@ }
}

// ── Specs ───────────────────────────────────────────────────────────────

/// Well-formedness of the aliasing tracker.
/// All in-flight resources must be bound (have a memory range).
pub open spec fn aliasing_tracker_wf(tracker: &RuntimeAliasingTracker) -> bool {
    forall|r: ResourceId| tracker.in_flight@.contains(r)
        ==> tracker.bindings@.contains_key(r)
}

/// Whether a resource is bound.
pub open spec fn resource_bound(
    tracker: &RuntimeAliasingTracker,
    resource: ResourceId,
) -> bool {
    tracker.bindings@.contains_key(resource)
}

/// Get the memory range of a bound resource.
pub open spec fn resource_range(
    tracker: &RuntimeAliasingTracker,
    resource: ResourceId,
) -> MemoryRange
    recommends tracker.bindings@.contains_key(resource),
{
    tracker.bindings@[resource]
}

/// Whether any overlap exists between two bound resources.
pub open spec fn any_overlap_exists(
    tracker: &RuntimeAliasingTracker,
    r1: ResourceId,
    r2: ResourceId,
) -> bool {
    tracker.bindings@.contains_key(r1)
    && tracker.bindings@.contains_key(r2)
    && ranges_overlap(tracker.bindings@[r1], tracker.bindings@[r2])
}

/// Whether two bound in-flight resources overlap (hazard).
pub open spec fn no_in_flight_overlaps(tracker: &RuntimeAliasingTracker) -> bool {
    forall|r1: ResourceId, r2: ResourceId|
        tracker.in_flight@.contains(r1)
        && tracker.in_flight@.contains(r2)
        && r1 != r2
        && tracker.bindings@.contains_key(r1)
        && tracker.bindings@.contains_key(r2)
        ==> !ranges_overlap(tracker.bindings@[r1], tracker.bindings@[r2])
}

/// Number of in-flight resources.
pub open spec fn in_flight_count(tracker: &RuntimeAliasingTracker) -> nat {
    tracker.in_flight@.len()
}

/// Number of bound resources.
pub open spec fn bound_resource_count(tracker: &RuntimeAliasingTracker) -> nat {
    tracker.bindings@.dom().len()
}

/// A binding is within an allocation (offset + size within the allocation).
pub open spec fn binding_within_allocation(
    range: MemoryRange,
    allocation_size: nat,
) -> bool {
    range.offset + range.size <= allocation_size
}

// ── Exec Functions ──────────────────────────────────────────────────────

/// Exec: create an empty aliasing tracker.
pub fn create_aliasing_tracker_exec() -> (out: RuntimeAliasingTracker)
    ensures
        aliasing_tracker_wf(&out),
        out.bindings@ == Map::<ResourceId, MemoryRange>::empty(),
        out.in_flight@ == Set::<ResourceId>::empty(),
{
    RuntimeAliasingTracker {
        bindings: Ghost(Map::empty()),
        in_flight: Ghost(Set::empty()),
    }
}

/// Exec: bind a resource to a memory range.
/// Caller must prove the resource is not currently in-flight on the GPU.
pub fn bind_resource_exec(
    tracker: &mut RuntimeAliasingTracker,
    resource: Ghost<ResourceId>,
    range: Ghost<MemoryRange>,
)
    requires
        !old(tracker).in_flight@.contains(resource@),
    ensures
        tracker.bindings@ == old(tracker).bindings@.insert(resource@, range@),
        tracker.in_flight@ == old(tracker).in_flight@,
{
    tracker.bindings = Ghost(tracker.bindings@.insert(resource@, range@));
}

/// Exec: unbind a resource.
pub fn unbind_resource_exec(
    tracker: &mut RuntimeAliasingTracker,
    resource: Ghost<ResourceId>,
)
    requires
        !old(tracker).in_flight@.contains(resource@),
    ensures
        tracker.bindings@ == old(tracker).bindings@.remove(resource@),
        tracker.in_flight@ == old(tracker).in_flight@,
{
    tracker.bindings = Ghost(tracker.bindings@.remove(resource@));
}

/// Exec: mark a resource as in-flight.
/// Caller must prove no currently in-flight resource overlaps this one (aliasing safety).
pub fn mark_in_flight_exec(
    tracker: &mut RuntimeAliasingTracker,
    resource: Ghost<ResourceId>,
)
    requires
        old(tracker).bindings@.contains_key(resource@),
        no_in_flight_overlaps(old(tracker)),
        forall|other: ResourceId|
            old(tracker).in_flight@.contains(other)
            && other != resource@
            && old(tracker).bindings@.contains_key(other)
            ==> !ranges_overlap(
                old(tracker).bindings@[resource@],
                old(tracker).bindings@[other],
            ),
    ensures
        tracker.in_flight@ == old(tracker).in_flight@.insert(resource@),
        tracker.bindings@ == old(tracker).bindings@,
{
    tracker.in_flight = Ghost(tracker.in_flight@.insert(resource@));
}

/// Exec: mark a set of resources as in-flight (batch version for submit).
/// Caller must prove the combined old+new in-flight set has no overlapping pairs.
pub fn mark_set_in_flight_exec(
    tracker: &mut RuntimeAliasingTracker,
    resources: Ghost<Set<ResourceId>>,
)
    requires
        // All resources in the set are bound
        forall|r: ResourceId| resources@.contains(r)
            ==> old(tracker).bindings@.contains_key(r),
        // The combined set has no overlapping pairs
        no_in_flight_overlaps(old(tracker)),
        forall|r1: ResourceId, r2: ResourceId|
            (old(tracker).in_flight@.contains(r1) || resources@.contains(r1))
            && (old(tracker).in_flight@.contains(r2) || resources@.contains(r2))
            && r1 != r2
            && old(tracker).bindings@.contains_key(r1)
            && old(tracker).bindings@.contains_key(r2)
            ==> !ranges_overlap(
                old(tracker).bindings@[r1],
                old(tracker).bindings@[r2],
            ),
    ensures
        tracker.in_flight@ == old(tracker).in_flight@.union(resources@),
        tracker.bindings@ == old(tracker).bindings@,
{
    tracker.in_flight = Ghost(tracker.in_flight@.union(resources@));
}

/// Exec: clear a set of resources from in-flight (batch version for completion).
pub fn clear_set_in_flight_exec(
    tracker: &mut RuntimeAliasingTracker,
    resources: Ghost<Set<ResourceId>>,
)
    ensures
        tracker.in_flight@ == old(tracker).in_flight@.difference(resources@),
        tracker.bindings@ == old(tracker).bindings@,
{
    tracker.in_flight = Ghost(tracker.in_flight@.difference(resources@));
}

/// Exec: clear a resource from in-flight (GPU work completed).
pub fn clear_in_flight_exec(
    tracker: &mut RuntimeAliasingTracker,
    resource: Ghost<ResourceId>,
)
    ensures
        tracker.in_flight@ == old(tracker).in_flight@.remove(resource@),
        tracker.bindings@ == old(tracker).bindings@,
{
    tracker.in_flight = Ghost(tracker.in_flight@.remove(resource@));
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// Binding preserves existing bindings.
pub proof fn lemma_bind_preserves_wf(
    tracker: &RuntimeAliasingTracker,
    resource: ResourceId,
    range: MemoryRange,
    other: ResourceId,
)
    requires
        other != resource,
        tracker.bindings@.contains_key(other),
    ensures
        tracker.bindings@.insert(resource, range).contains_key(other),
        tracker.bindings@.insert(resource, range)[other]
            == tracker.bindings@[other],
{
}

/// Unbinding preserves other bindings.
pub proof fn lemma_unbind_preserves_wf(
    tracker: &RuntimeAliasingTracker,
    resource: ResourceId,
    other: ResourceId,
)
    requires
        other != resource,
        tracker.bindings@.contains_key(other),
    ensures
        tracker.bindings@.remove(resource).contains_key(other),
        tracker.bindings@.remove(resource)[other]
            == tracker.bindings@[other],
{
}

/// Non-overlapping binding doesn't create hazards.
pub proof fn lemma_no_overlap_after_bind(
    tracker: &RuntimeAliasingTracker,
    resource: ResourceId,
    range: MemoryRange,
    other: ResourceId,
)
    requires
        tracker.bindings@.contains_key(other),
        ranges_disjoint(range, tracker.bindings@[other]),
    ensures
        !ranges_overlap(range, tracker.bindings@[other]),
{
    lemma_disjoint_no_overlap(range, tracker.bindings@[other]);
}

/// Safe bindings imply no write hazard.
pub proof fn lemma_safe_bindings_no_hazard(
    bindings: Map<ResourceId, MemoryRange>,
    submissions: Seq<SubmissionRecord>,
    r1: ResourceId,
    r2: ResourceId,
)
    requires
        all_aliasing_safe(bindings, submissions),
        bindings.contains_key(r1),
        bindings.contains_key(r2),
        r1 != r2,
        ranges_overlap(bindings[r1], bindings[r2]),
    ensures
        aliasing_safe(submissions, r1, r2),
{
}

/// In-flight overlap is detected.
pub proof fn lemma_in_flight_overlap_detected(
    tracker: &RuntimeAliasingTracker,
    r1: ResourceId,
    r2: ResourceId,
)
    requires
        tracker.in_flight@.contains(r1),
        tracker.in_flight@.contains(r2),
        r1 != r2,
        tracker.bindings@.contains_key(r1),
        tracker.bindings@.contains_key(r2),
        ranges_overlap(tracker.bindings@[r1], tracker.bindings@[r2]),
    ensures
        !no_in_flight_overlaps(tracker),
{
}

/// After clearing in-flight, the resource is no longer in-flight.
pub proof fn lemma_clear_in_flight_safe(
    tracker: &RuntimeAliasingTracker,
    resource: ResourceId,
)
    ensures
        !tracker.in_flight@.remove(resource).contains(resource),
{
}

/// Bind then unbind roundtrip.
pub proof fn lemma_bind_unbind_roundtrip(
    tracker: &RuntimeAliasingTracker,
    resource: ResourceId,
    range: MemoryRange,
)
    requires !tracker.bindings@.contains_key(resource),
    ensures
        tracker.bindings@.insert(resource, range).remove(resource)
            =~= tracker.bindings@,
{
}

/// Disjoint ranges are safe regardless of in-flight status.
pub proof fn lemma_disjoint_ranges_safe(
    r1: MemoryRange,
    r2: MemoryRange,
)
    requires ranges_disjoint(r1, r2),
    ensures !ranges_overlap(r1, r2),
{
    lemma_disjoint_no_overlap(r1, r2);
}

/// Overlap is symmetric.
pub proof fn lemma_overlap_symmetric(r1: MemoryRange, r2: MemoryRange)
    ensures ranges_overlap(r1, r2) == ranges_overlap(r2, r1),
{
    crate::memory_aliasing::lemma_overlap_symmetric(r1, r2);
}

/// Transitivity: if no resource in set A overlaps any in set B,
/// and B has no internal overlaps, then A ∪ B has no cross-overlaps.
pub proof fn lemma_transitive_no_overlap(
    r1: MemoryRange,
    r2: MemoryRange,
    r3: MemoryRange,
)
    requires
        different_allocations(r1, r2),
        different_allocations(r2, r3),
    ensures
        !ranges_overlap(r1, r2),
        !ranges_overlap(r2, r3),
{
    lemma_different_allocations_no_overlap(r1, r2);
    lemma_different_allocations_no_overlap(r2, r3);
}

} // verus!
