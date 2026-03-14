use vstd::prelude::*;
use crate::resource::*;
use crate::memory::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// Memory mapping state for a memory allocation.
pub struct MemoryMapState {
    pub allocation_id: nat,
    /// Whether the memory is currently mapped.
    pub mapped: bool,
    /// Mapped offset (valid when mapped).
    pub map_offset: nat,
    /// Mapped size (valid when mapped).
    pub map_size: nat,
    /// Whether the memory type is host-visible (required for mapping).
    pub host_visible: bool,
    /// Total allocation size in bytes.
    pub allocation_size: nat,
    /// Whether the memory type is host-coherent.
    pub host_coherent: bool,
    /// Whether a flush is pending (non-coherent only).
    pub flush_pending: bool,
    /// Whether an invalidate has been done since last GPU write (non-coherent only).
    pub invalidated: bool,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// Map memory for host access.
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

/// Unmap memory.
pub open spec fn unmap_memory(state: MemoryMapState) -> MemoryMapState {
    MemoryMapState {
        mapped: false,
        ..state
    }
}

/// Host write to mapped memory (marks flush as pending for non-coherent).
pub open spec fn host_write(state: MemoryMapState) -> MemoryMapState {
    MemoryMapState {
        flush_pending: !state.host_coherent,
        ..state
    }
}

/// Flush mapped memory range (makes host writes visible to device).
pub open spec fn flush_memory(state: MemoryMapState) -> MemoryMapState {
    MemoryMapState {
        flush_pending: false,
        ..state
    }
}

/// Invalidate mapped memory range (makes device writes visible to host).
pub open spec fn invalidate_memory(state: MemoryMapState) -> MemoryMapState {
    MemoryMapState {
        invalidated: true,
        ..state
    }
}

/// Host can safely read the mapped memory.
pub open spec fn host_read_safe(state: MemoryMapState) -> bool {
    state.mapped
    && (state.host_coherent || state.invalidated)
}

/// Host writes are visible to the device.
pub open spec fn host_writes_visible(state: MemoryMapState) -> bool {
    state.host_coherent || !state.flush_pending
}

/// Memory can be mapped: not already mapped and memory type is host-visible.
pub open spec fn can_map(state: MemoryMapState) -> bool {
    !state.mapped
    && state.host_visible
}

/// A map range is valid: non-zero size and within the allocation.
pub open spec fn map_range_valid(state: MemoryMapState, offset: nat, size: nat) -> bool {
    size > 0
    && offset + size <= state.allocation_size
}

/// An access is within the mapped range.
pub open spec fn access_in_mapped_range(
    state: MemoryMapState,
    offset: nat,
    size: nat,
) -> bool {
    state.mapped
    && offset >= state.map_offset
    && offset + size <= state.map_offset + state.map_size
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// After mapping, the memory is mapped.
pub proof fn lemma_map_makes_mapped(
    state: MemoryMapState,
    offset: nat,
    size: nat,
)
    ensures map_memory(state, offset, size).mapped,
{
}

/// After unmapping, the memory is not mapped.
pub proof fn lemma_unmap_makes_unmapped(state: MemoryMapState)
    ensures !unmap_memory(state).mapped,
{
}

/// Coherent memory is always host-read-safe when mapped.
pub proof fn lemma_coherent_always_readable(state: MemoryMapState)
    requires state.mapped, state.host_coherent,
    ensures host_read_safe(state),
{
}

/// Non-coherent memory needs invalidate before host read.
pub proof fn lemma_non_coherent_needs_invalidate(state: MemoryMapState)
    requires
        state.mapped,
        !state.host_coherent,
        !state.invalidated,
    ensures
        !host_read_safe(state),
{
}

/// After invalidate, non-coherent memory is readable.
pub proof fn lemma_invalidate_enables_read(state: MemoryMapState)
    requires state.mapped,
    ensures host_read_safe(invalidate_memory(state)),
{
}

/// After flush, host writes are visible.
pub proof fn lemma_flush_makes_visible(state: MemoryMapState)
    ensures host_writes_visible(flush_memory(state)),
{
}

/// Coherent memory never needs flush.
pub proof fn lemma_coherent_no_flush_needed(state: MemoryMapState)
    requires state.host_coherent,
    ensures host_writes_visible(state),
{
}

/// Host write on coherent memory doesn't set flush_pending.
pub proof fn lemma_coherent_write_no_flush(state: MemoryMapState)
    requires state.host_coherent,
    ensures !host_write(state).flush_pending,
{
}

/// Non-host-visible memory cannot be mapped.
pub proof fn lemma_non_host_visible_cannot_map(state: MemoryMapState)
    requires !state.host_visible,
    ensures !can_map(state),
{
}

/// A valid map range stays within the allocation.
pub proof fn lemma_map_range_within_allocation(state: MemoryMapState, offset: nat, size: nat)
    requires map_range_valid(state, offset, size),
    ensures offset + size <= state.allocation_size,
{
}

} // verus!
