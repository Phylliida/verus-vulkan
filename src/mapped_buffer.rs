use vstd::prelude::*;

verus! {

/// Ownership state of a host-mapped GPU buffer.
pub enum BufferOwnership {
    /// CPU can read/write the mapped memory.
    HostOwned,
    /// Buffer is in a GPU submission — CPU must not touch it.
    GpuPending,
}

/// Ghost model for a persistently-mapped GPU buffer.
pub struct MappedBufferState {
    pub id: nat,
    pub size: nat,
    pub ownership: BufferOwnership,
}

/// Predicate: buffer is host-writable.
pub open spec fn buffer_host_owned(s: MappedBufferState) -> bool {
    s.ownership == BufferOwnership::HostOwned
}

/// Ghost transition: GPU work is done, host reclaims the buffer.
pub open spec fn reclaim_ghost(s: MappedBufferState) -> MappedBufferState {
    MappedBufferState { ownership: BufferOwnership::HostOwned, ..s }
}

/// Ghost transition: host releases the buffer for GPU use.
pub open spec fn release_ghost(s: MappedBufferState) -> MappedBufferState {
    MappedBufferState { ownership: BufferOwnership::GpuPending, ..s }
}

/// Well-formedness: buffer has a positive size.
pub open spec fn mapped_buffer_wf(s: MappedBufferState) -> bool {
    s.size > 0
}

// ── Lemmas ──────────────────────────────────────────────────────────────

pub proof fn lemma_reclaim_makes_host_owned(s: MappedBufferState)
    ensures buffer_host_owned(reclaim_ghost(s))
{}

pub proof fn lemma_release_makes_gpu_pending(s: MappedBufferState)
    ensures !buffer_host_owned(release_ghost(s))
{}

pub proof fn lemma_reclaim_preserves_id_size(s: MappedBufferState)
    ensures
        reclaim_ghost(s).id == s.id,
        reclaim_ghost(s).size == s.size,
{}

pub proof fn lemma_release_preserves_id_size(s: MappedBufferState)
    ensures
        release_ghost(s).id == s.id,
        release_ghost(s).size == s.size,
{}

} // verus!
