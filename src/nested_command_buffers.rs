use vstd::prelude::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// State for nested command buffer execution tracking.
pub struct NestedCommandBufferState {
    pub nesting_level: nat,
    pub max_nesting_level: nat,
    pub state_isolated: bool,
    pub parent_render_pass: Option<nat>,
}

/// Device limits for nested command buffers.
pub struct NestedCommandBufferLimits {
    pub max_command_buffer_nesting_level: nat,
    pub supports_render_pass_inheritance: bool,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// A nested command buffer state is well-formed.
pub open spec fn nested_cb_well_formed(
    state: NestedCommandBufferState,
    limits: NestedCommandBufferLimits,
) -> bool {
    state.nesting_level <= state.max_nesting_level
    && state.max_nesting_level <= limits.max_command_buffer_nesting_level
}

/// Whether further nesting is possible.
pub open spec fn can_nest_deeper(
    state: NestedCommandBufferState,
    limits: NestedCommandBufferLimits,
) -> bool {
    state.nesting_level < state.max_nesting_level
    && state.max_nesting_level <= limits.max_command_buffer_nesting_level
}

/// Ghost update: nest one level deeper.
pub open spec fn nest_command_buffer(
    state: NestedCommandBufferState,
) -> NestedCommandBufferState {
    NestedCommandBufferState {
        nesting_level: state.nesting_level + 1,
        state_isolated: true,
        ..state
    }
}

/// Ghost update: unnest one level.
pub open spec fn unnest_command_buffer(
    state: NestedCommandBufferState,
) -> NestedCommandBufferState
    recommends state.nesting_level > 0,
{
    NestedCommandBufferState {
        nesting_level: (state.nesting_level - 1) as nat,
        state_isolated: false,
        ..state
    }
}

/// Initial nesting state at the top level.
pub open spec fn initial_nesting_state(
    limits: NestedCommandBufferLimits,
) -> NestedCommandBufferState {
    NestedCommandBufferState {
        nesting_level: 0,
        max_nesting_level: limits.max_command_buffer_nesting_level,
        state_isolated: false,
        parent_render_pass: None,
    }
}

/// A nested render pass execution is valid.
pub open spec fn nested_render_pass_valid(
    state: NestedCommandBufferState,
    limits: NestedCommandBufferLimits,
) -> bool {
    limits.supports_render_pass_inheritance || matches!(state.parent_render_pass, None)
}

/// Current nesting depth.
pub open spec fn nesting_depth(state: NestedCommandBufferState) -> nat {
    state.nesting_level
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// Initial state is well-formed when max > 0.
pub proof fn lemma_initial_well_formed(limits: NestedCommandBufferLimits)
    requires limits.max_command_buffer_nesting_level > 0,
    ensures nested_cb_well_formed(initial_nesting_state(limits), limits),
{
}

/// Initial state has nesting depth 0.
pub proof fn lemma_initial_level_zero(limits: NestedCommandBufferLimits)
    ensures nesting_depth(initial_nesting_state(limits)) == 0,
{
}

/// Nesting increments the level.
pub proof fn lemma_nest_increments_level(state: NestedCommandBufferState)
    ensures nesting_depth(nest_command_buffer(state)) == nesting_depth(state) + 1,
{
}

/// Unnesting decrements the level.
pub proof fn lemma_unnest_decrements_level(state: NestedCommandBufferState)
    requires state.nesting_level > 0,
    ensures nesting_depth(unnest_command_buffer(state)) == nesting_depth(state) - 1,
{
}

/// Nest then unnest restores the original nesting level.
pub proof fn lemma_nest_unnest_roundtrip(state: NestedCommandBufferState)
    ensures
        nesting_depth(unnest_command_buffer(nest_command_buffer(state)))
            == nesting_depth(state),
{
}

/// Nesting sets state_isolated to true.
pub proof fn lemma_nest_isolates_state(state: NestedCommandBufferState)
    ensures nest_command_buffer(state).state_isolated,
{
}

/// Nesting preserves parent_render_pass.
pub proof fn lemma_nested_preserves_parent(state: NestedCommandBufferState)
    ensures nest_command_buffer(state).parent_render_pass == state.parent_render_pass,
{
}

/// Initial state is not isolated.
pub proof fn lemma_initial_not_isolated(limits: NestedCommandBufferLimits)
    ensures !initial_nesting_state(limits).state_isolated,
{
}

/// Can nest + well-formed implies well-formed after nesting.
pub proof fn lemma_can_nest_implies_well_formed_after(
    state: NestedCommandBufferState,
    limits: NestedCommandBufferLimits,
)
    requires
        nested_cb_well_formed(state, limits),
        can_nest_deeper(state, limits),
    ensures nested_cb_well_formed(nest_command_buffer(state), limits),
{
}

} // verus!
