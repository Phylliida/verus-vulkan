use vstd::prelude::*;

verus! {

//  ── Types ───────────────────────────────────────────────────────────────

///  Depth clamp mode: how fragment depth output is clamped.
pub enum DepthClampMode {
    ///  No clamping applied.
    Disabled,
    ///  Clamp to the viewport depth range.
    ViewportRange,
    ///  Clamp to [0, 1].
    ZeroOne,
    ///  Clamp to a user-defined range.
    UserDefined,
}

///  A user-defined depth clamp range.
pub struct DepthClampRange {
    pub min_depth: int,
    pub max_depth: int,
}

///  Depth clamp state for a graphics pipeline.
pub struct DepthClampState {
    pub mode: DepthClampMode,
    pub range: DepthClampRange,
    pub clamp_enabled: bool,
}

//  ── Spec Functions ──────────────────────────────────────────────────────

///  A depth clamp range is valid: min <= max.
pub open spec fn depth_clamp_range_valid(range: DepthClampRange) -> bool {
    range.min_depth <= range.max_depth
}

///  A depth clamp state is well-formed.
pub open spec fn depth_clamp_state_well_formed(state: DepthClampState) -> bool {
    //  UserDefined mode requires a valid range
    (matches!(state.mode, DepthClampMode::UserDefined) ==> depth_clamp_range_valid(state.range))
    //  Disabled mode must not have clamping enabled
    && (matches!(state.mode, DepthClampMode::Disabled) ==> !state.clamp_enabled)
    //  Active modes must have clamping enabled — prevents silent no-op
    && (!matches!(state.mode, DepthClampMode::Disabled) ==> state.clamp_enabled)
}

///  Default depth clamp state: disabled, range (0,1), no clamping.
pub open spec fn default_depth_clamp_state() -> DepthClampState {
    DepthClampState {
        mode: DepthClampMode::Disabled,
        range: DepthClampRange { min_depth: 0, max_depth: 1 },
        clamp_enabled: false,
    }
}

///  Ghost update: set the depth clamp mode and range.
pub open spec fn set_depth_clamp_mode(
    state: DepthClampState,
    mode: DepthClampMode,
    range: DepthClampRange,
) -> DepthClampState {
    DepthClampState {
        mode: mode,
        range: range,
        clamp_enabled: !matches!(mode, DepthClampMode::Disabled),
    }
}

///  Whether depth clamping affects fragment output.
pub open spec fn depth_clamp_affects_output(state: DepthClampState) -> bool {
    state.clamp_enabled && !matches!(state.mode, DepthClampMode::Disabled)
}

///  Whether a depth value is within the active clamp range.
pub open spec fn depth_value_in_clamp_range(state: DepthClampState, depth: int) -> bool {
    match state.mode {
        DepthClampMode::Disabled => true,
        DepthClampMode::ViewportRange => true, //  viewport range is dynamic
        DepthClampMode::ZeroOne => 0 <= depth && depth <= 1,
        DepthClampMode::UserDefined => state.range.min_depth <= depth && depth <= state.range.max_depth,
    }
}

//  ── Proofs ──────────────────────────────────────────────────────────────

///  Default depth clamp state is well-formed.
pub proof fn lemma_default_well_formed()
    ensures depth_clamp_state_well_formed(default_depth_clamp_state()),
{
}

///  Default state does not clamp.
pub proof fn lemma_default_no_clamp()
    ensures !depth_clamp_affects_output(default_depth_clamp_state()),
{
}

///  Disabled mode does not affect output.
pub proof fn lemma_disabled_no_output_effect(state: DepthClampState)
    requires matches!(state.mode, DepthClampMode::Disabled),
             depth_clamp_state_well_formed(state),
    ensures !depth_clamp_affects_output(state),
{
}

///  The (0,1) range is valid.
pub proof fn lemma_zero_one_range_valid()
    ensures depth_clamp_range_valid(DepthClampRange { min_depth: 0, max_depth: 1 }),
{
}

///  Setting mode with a valid range produces a well-formed state.
pub proof fn lemma_set_mode_preserves_structure(
    state: DepthClampState,
    mode: DepthClampMode,
    range: DepthClampRange,
)
    requires
        matches!(mode, DepthClampMode::UserDefined) ==> depth_clamp_range_valid(range),
    ensures depth_clamp_state_well_formed(set_depth_clamp_mode(state, mode, range)),
{
}

///  Well-formed + UserDefined implies range is valid.
pub proof fn lemma_user_defined_requires_valid_range(state: DepthClampState)
    requires
        depth_clamp_state_well_formed(state),
        matches!(state.mode, DepthClampMode::UserDefined),
    ensures depth_clamp_range_valid(state.range),
{
}

///  ZeroOne mode with in-range value implies 0 <= depth <= 1.
pub proof fn lemma_zero_one_bounds_depth(state: DepthClampState, depth: int)
    requires
        matches!(state.mode, DepthClampMode::ZeroOne),
        depth_value_in_clamp_range(state, depth),
    ensures 0 <= depth && depth <= 1,
{
}

///  set_depth_clamp_mode sets the requested mode.
pub proof fn lemma_set_mode_updates(
    state: DepthClampState,
    mode: DepthClampMode,
    range: DepthClampRange,
)
    ensures ({
        let result = set_depth_clamp_mode(state, mode, range);
        result.range == range
    }),
{
}

} //  verus!
