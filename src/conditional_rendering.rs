use vstd::prelude::*;
use crate::memory::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// Ghost state for conditional rendering (VK_EXT_conditional_rendering).
///
/// When conditional rendering is active, draw/dispatch commands are
/// only executed if the predicate buffer contains a non-zero value.
pub struct ConditionalRenderingState {
    /// Whether conditional rendering is active.
    pub active: bool,
    /// The predicate buffer id (valid when active).
    pub predicate_buffer: nat,
    /// Offset into the predicate buffer.
    pub predicate_offset: nat,
    /// Whether the condition is inverted.
    pub inverted: bool,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// Initial state: no conditional rendering active.
pub open spec fn no_conditional_rendering() -> ConditionalRenderingState {
    ConditionalRenderingState {
        active: false,
        predicate_buffer: 0,
        predicate_offset: 0,
        inverted: false,
    }
}

/// Begin conditional rendering.
pub open spec fn begin_conditional(
    buffer_id: nat,
    offset: nat,
    inverted: bool,
) -> ConditionalRenderingState {
    ConditionalRenderingState {
        active: true,
        predicate_buffer: buffer_id,
        predicate_offset: offset,
        inverted,
    }
}

/// End conditional rendering.
pub open spec fn end_conditional() -> ConditionalRenderingState {
    no_conditional_rendering()
}

/// Conditional rendering begin is valid: buffer must be alive and have
/// enough space for the predicate value (4 bytes).
pub open spec fn begin_conditional_valid(
    buffer: BufferState,
    offset: nat,
) -> bool {
    buffer.alive
    && offset + 4 <= buffer.size
}

/// A draw/dispatch command is conditionally executed.
pub open spec fn command_is_conditional(
    state: ConditionalRenderingState,
) -> bool {
    state.active
}

/// Conditional rendering is not active (commands execute unconditionally).
pub open spec fn commands_unconditional(
    state: ConditionalRenderingState,
) -> bool {
    !state.active
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// Initial state has no conditional rendering.
pub proof fn lemma_initial_unconditional()
    ensures commands_unconditional(no_conditional_rendering()),
{
}

/// After begin, conditional rendering is active.
pub proof fn lemma_begin_makes_conditional(
    buffer_id: nat,
    offset: nat,
    inverted: bool,
)
    ensures
        command_is_conditional(begin_conditional(buffer_id, offset, inverted)),
{
}

/// After end, commands are unconditional.
pub proof fn lemma_end_makes_unconditional()
    ensures commands_unconditional(end_conditional()),
{
}

/// Begin/end round-trip returns to unconditional.
pub proof fn lemma_begin_end_roundtrip()
    ensures commands_unconditional(end_conditional()),
{
}

/// Valid begin requires buffer to hold a 32-bit predicate.
pub proof fn lemma_valid_begin_needs_4_bytes(
    buffer: BufferState,
    offset: nat,
)
    requires begin_conditional_valid(buffer, offset),
    ensures offset + 4 <= buffer.size,
{
}

} // verus!
