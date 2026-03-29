use vstd::prelude::*;
use crate::resource::*;
use crate::memory::*;
use crate::lifetime::*;

verus! {

//  ── Types ───────────────────────────────────────────────────────────────

///  Memory mapping state for a memory allocation.
pub struct MemoryMapState {
    pub allocation_id: nat,
    ///  Whether the memory is currently mapped.
    pub mapped: bool,
    ///  Mapped offset (valid when mapped).
    pub map_offset: nat,
    ///  Mapped size (valid when mapped).
    pub map_size: nat,
    ///  Whether the memory type is host-visible (required for mapping).
    pub host_visible: bool,
    ///  Total allocation size in bytes.
    pub allocation_size: nat,
    ///  Whether the memory type is host-coherent.
    pub host_coherent: bool,
    ///  Whether a flush is pending (non-coherent only).
    pub flush_pending: bool,
    ///  Whether an invalidate has been done since last GPU write (non-coherent only).
    pub invalidated: bool,
}

//  ── Spec Functions ──────────────────────────────────────────────────────

///  Map memory for host access.
pub open spec fn map_memory(
    state: MemoryMapState,
    offset: nat,
    size: nat,
) -> MemoryMapState
    recommends can_map(state), map_range_valid(state, offset, size),
{
    MemoryMapState {
        mapped: true,
        map_offset: offset,
        map_size: size,
        ..state
    }
}

///  Unmap memory.
pub open spec fn unmap_memory(state: MemoryMapState) -> MemoryMapState
    recommends state.mapped,
{
    MemoryMapState {
        mapped: false,
        ..state
    }
}

///  Host write to mapped memory (marks flush as pending for non-coherent).
pub open spec fn host_write(state: MemoryMapState) -> MemoryMapState
    recommends state.mapped,
{
    MemoryMapState {
        flush_pending: !state.host_coherent,
        ..state
    }
}

///  Flush mapped memory range (makes host writes visible to device).
pub open spec fn flush_memory(state: MemoryMapState) -> MemoryMapState
    recommends state.mapped,
{
    MemoryMapState {
        flush_pending: false,
        ..state
    }
}

///  Invalidate mapped memory range (makes device writes visible to host).
pub open spec fn invalidate_memory(state: MemoryMapState) -> MemoryMapState
    recommends state.mapped,
{
    MemoryMapState {
        invalidated: true,
        ..state
    }
}

///  Host can safely read the mapped memory.
pub open spec fn host_read_safe(state: MemoryMapState) -> bool {
    state.mapped
    && (state.host_coherent || state.invalidated)
}

///  Host writes are visible to the device.
pub open spec fn host_writes_visible(state: MemoryMapState) -> bool {
    state.host_coherent || !state.flush_pending
}

///  Memory can be mapped: not already mapped and memory type is host-visible.
pub open spec fn can_map(state: MemoryMapState) -> bool {
    !state.mapped
    && state.host_visible
}

///  A map range is valid: non-zero size and within the allocation.
pub open spec fn map_range_valid(state: MemoryMapState, offset: nat, size: nat) -> bool {
    size > 0
    && offset + size <= state.allocation_size
}

///  An access is within the mapped range.
pub open spec fn access_in_mapped_range(
    state: MemoryMapState,
    offset: nat,
    size: nat,
) -> bool {
    state.mapped
    && offset >= state.map_offset
    && offset + size <= state.map_offset + state.map_size
}

///  Host can safely write to a mapped buffer: no pending GPU references.
///  Mirrors `host_readable` from readback.rs.
pub open spec fn host_writable(
    submissions: Seq<SubmissionRecord>,
    resource: ResourceId,
) -> bool {
    no_pending_references(submissions, resource)
}

//  ── Flush-Before-Submit ─────────────────────────────────────────────────

///  All mapped resources referenced by a submission have visible host writes.
///  Prevents submitting work that reads stale data from non-coherent memory.
pub open spec fn submission_writes_visible(
    mapped_states: Map<ResourceId, MemoryMapState>,
    referenced: Set<ResourceId>,
) -> bool {
    forall|r: ResourceId| referenced.contains(r) && mapped_states.contains_key(r)
        ==> host_writes_visible(#[trigger] mapped_states[r])
}

//  ── Proofs ──────────────────────────────────────────────────────────────

///  After mapping, the memory is mapped.
pub proof fn lemma_map_makes_mapped(
    state: MemoryMapState,
    offset: nat,
    size: nat,
)
    ensures map_memory(state, offset, size).mapped,
{
}

///  After unmapping, the memory is not mapped.
pub proof fn lemma_unmap_makes_unmapped(state: MemoryMapState)
    ensures !unmap_memory(state).mapped,
{
}

///  Coherent memory is always host-read-safe when mapped.
pub proof fn lemma_coherent_always_readable(state: MemoryMapState)
    requires state.mapped, state.host_coherent,
    ensures host_read_safe(state),
{
}

///  Non-coherent memory needs invalidate before host read.
pub proof fn lemma_non_coherent_needs_invalidate(state: MemoryMapState)
    requires
        state.mapped,
        !state.host_coherent,
        !state.invalidated,
    ensures
        !host_read_safe(state),
{
}

///  After invalidate, non-coherent memory is readable.
pub proof fn lemma_invalidate_enables_read(state: MemoryMapState)
    requires state.mapped,
    ensures host_read_safe(invalidate_memory(state)),
{
}

///  After flush, host writes are visible.
pub proof fn lemma_flush_makes_visible(state: MemoryMapState)
    ensures host_writes_visible(flush_memory(state)),
{
}

///  Coherent memory never needs flush.
pub proof fn lemma_coherent_no_flush_needed(state: MemoryMapState)
    requires state.host_coherent,
    ensures host_writes_visible(state),
{
}

///  Host write on coherent memory doesn't set flush_pending.
pub proof fn lemma_coherent_write_no_flush(state: MemoryMapState)
    requires state.host_coherent,
    ensures !host_write(state).flush_pending,
{
}

///  Non-host-visible memory cannot be mapped.
pub proof fn lemma_non_host_visible_cannot_map(state: MemoryMapState)
    requires !state.host_visible,
    ensures !can_map(state),
{
}

///  A valid map range stays within the allocation.
pub proof fn lemma_map_range_within_allocation(state: MemoryMapState, offset: nat, size: nat)
    requires map_range_valid(state, offset, size),
    ensures offset + size <= state.allocation_size,
{
}

///  Double-mapping is invalid.
pub proof fn lemma_double_map_invalid(state: MemoryMapState)
    requires state.mapped,
    ensures !can_map(state),
{
}

//  ── Flush-Before-Submit Proofs ──────────────────────────────────────────

///  If no referenced resources are mapped, writes are trivially visible.
pub proof fn lemma_no_mapped_writes_visible(
    mapped_states: Map<ResourceId, MemoryMapState>,
    referenced: Set<ResourceId>,
)
    requires
        forall|r: ResourceId| referenced.contains(r)
            ==> !mapped_states.contains_key(r),
    ensures
        submission_writes_visible(mapped_states, referenced),
{}

///  All coherent mapped resources trivially have visible writes.
pub proof fn lemma_coherent_writes_visible(
    mapped_states: Map<ResourceId, MemoryMapState>,
    referenced: Set<ResourceId>,
)
    requires
        forall|r: ResourceId| referenced.contains(r) && mapped_states.contains_key(r)
            ==> (#[trigger] mapped_states[r]).host_coherent,
    ensures
        submission_writes_visible(mapped_states, referenced),
{}

///  After flushing all mapped resources, writes are visible.
pub proof fn lemma_flushed_writes_visible(
    mapped_states: Map<ResourceId, MemoryMapState>,
    referenced: Set<ResourceId>,
)
    requires
        forall|r: ResourceId| referenced.contains(r) && mapped_states.contains_key(r)
            ==> host_writes_visible(#[trigger] mapped_states[r]),
    ensures
        submission_writes_visible(mapped_states, referenced),
{}

//  ── Host-Writable Proofs ────────────────────────────────────────────────

///  After device_wait_idle (empty submissions), any resource is host-writable.
pub proof fn lemma_device_idle_host_writable(resource: ResourceId)
    ensures host_writable(Seq::<SubmissionRecord>::empty(), resource),
{
}

///  A freshly created resource (never submitted) is host-writable.
pub proof fn lemma_fresh_resource_host_writable(
    submissions: Seq<SubmissionRecord>,
    resource: ResourceId,
)
    requires
        forall|i: int| #![trigger submissions[i]]
            0 <= i < submissions.len()
            ==> !submissions[i].referenced_resources.contains(resource),
    ensures
        host_writable(submissions, resource),
{
}

///  After fence wait, resource is host-writable if all its submissions used that fence.
pub proof fn lemma_fence_wait_host_writable(
    submissions: Seq<SubmissionRecord>,
    fence: nat,
    resource: ResourceId,
)
    requires
        forall|i: int| 0 <= i < submissions.len()
            && submissions[i].referenced_resources.contains(resource)
            ==> submissions[i].fence_id == Some(fence),
    ensures
        host_writable(
            remove_completed(mark_fence_completed(submissions, fence)),
            resource,
        ),
{
    lemma_wait_clears_fence_submissions(submissions, fence, resource);
}

} //  verus!
