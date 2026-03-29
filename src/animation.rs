use vstd::prelude::*;

verus! {

//  ── Types ───────────────────────────────────────────────────────────────

///  Ghost state for a single animation parameter across frames.
///
///  Animation parameters (e.g., bone transforms, material properties,
///  camera position) must change smoothly between frames to avoid visual
///  pops. This module proves that linear interpolation and frame-cycle
///  bounded updates preserve continuity invariants.
pub struct AnimationParameter {
    ///  Current value (abstract — could be a float, quaternion, etc.).
    pub value: int,
    ///  Value at the previous frame.
    pub prev_value: int,
    ///  Maximum allowed change per frame.
    pub max_delta: nat,
}

///  Ghost state for a set of animation parameters across frames.
pub struct AnimationState {
    ///  Current parameter values, indexed by parameter id.
    pub parameters: Map<nat, AnimationParameter>,
    ///  Frame counter.
    pub frame: nat,
}

//  ── Spec Functions ──────────────────────────────────────────────────────

///  A single parameter is continuous: the change from prev to current
///  is within the allowed delta.
pub open spec fn parameter_continuous(param: AnimationParameter) -> bool {
    abs_diff(param.value, param.prev_value) <= param.max_delta as int
}

///  Absolute difference helper.
pub open spec fn abs_diff(a: int, b: int) -> nat {
    if a >= b {
        (a - b) as nat
    } else {
        (b - a) as nat
    }
}

///  All parameters in an animation state are continuous.
pub open spec fn animation_continuous(state: AnimationState) -> bool {
    forall|id: nat| state.parameters.contains_key(id)
        ==> parameter_continuous(state.parameters[id])
}

///  Linear interpolation between two values.
///  t is in [0, max_t], result = a + (b - a) * t / max_t.
///  We use integer arithmetic: result = a * (max_t - t) + b * t, all divided by max_t.
///  For ghost purposes we just track the endpoints and t.
pub open spec fn lerp(a: int, b: int, t: nat, max_t: nat) -> int
    recommends max_t > 0,
{
    a + ((b - a) * (t as int)) / (max_t as int)
}

///  Advance a parameter by linear interpolation from prev to target.
pub open spec fn advance_parameter_lerp(
    param: AnimationParameter,
    target: int,
    max_delta: nat,
) -> AnimationParameter {
    let new_value = if abs_diff(target, param.value) <= max_delta as int {
        target
    } else if target > param.value {
        param.value + max_delta as int
    } else {
        param.value - max_delta as int
    };
    AnimationParameter {
        value: new_value,
        prev_value: param.value,
        max_delta: max_delta,
    }
}

///  Advance all parameters toward their targets, clamping to max_delta.
pub open spec fn advance_animation(
    state: AnimationState,
    targets: Map<nat, int>,
) -> AnimationState {
    AnimationState {
        parameters: Map::new(
            |id: nat| state.parameters.contains_key(id),
            |id: nat| {
                let param = state.parameters[id];
                let target = if targets.contains_key(id) {
                    targets[id]
                } else {
                    param.value //  hold steady
                };
                advance_parameter_lerp(param, target, param.max_delta)
            },
        ),
        frame: state.frame + 1,
    }
}

///  A parameter that holds steady (target == current value).
pub open spec fn parameter_steady(param: AnimationParameter) -> bool {
    param.value == param.prev_value
}

///  An animation is steady: all parameters are unchanged.
pub open spec fn animation_steady(state: AnimationState) -> bool {
    forall|id: nat| state.parameters.contains_key(id)
        ==> parameter_steady(state.parameters[id])
}

///  Create an initial animation parameter at a given value.
pub open spec fn initial_parameter(value: int, max_delta: nat) -> AnimationParameter {
    AnimationParameter {
        value: value,
        prev_value: value,
        max_delta: max_delta,
    }
}

//  ── Proofs ──────────────────────────────────────────────────────────────

///  abs_diff is symmetric.
pub proof fn lemma_abs_diff_symmetric(a: int, b: int)
    ensures abs_diff(a, b) == abs_diff(b, a),
{
}

///  abs_diff(a, a) == 0.
pub proof fn lemma_abs_diff_self(a: int)
    ensures abs_diff(a, a) == 0nat,
{
}

///  An initial parameter is continuous (delta is 0).
pub proof fn lemma_initial_parameter_continuous(value: int, max_delta: nat)
    ensures parameter_continuous(initial_parameter(value, max_delta)),
{
    lemma_abs_diff_self(value);
}

///  Advancing a parameter with clamping preserves continuity.
pub proof fn lemma_advance_preserves_continuity(
    param: AnimationParameter,
    target: int,
)
    ensures
        parameter_continuous(advance_parameter_lerp(param, target, param.max_delta)),
{
    let result = advance_parameter_lerp(param, target, param.max_delta);
    //  Case 1: |target - value| <= max_delta → new_value = target, prev = value
    //    |target - value| <= max_delta ✓
    //  Case 2: target > value → new_value = value + max_delta, prev = value
    //    |new_value - prev| = max_delta ✓
    //  Case 3: target < value → new_value = value - max_delta, prev = value
    //    |new_value - prev| = max_delta ✓
    assert(abs_diff(result.value, result.prev_value) <= param.max_delta as int);
}

///  Advancing all parameters preserves animation continuity.
pub proof fn lemma_advance_animation_continuous(
    state: AnimationState,
    targets: Map<nat, int>,
)
    ensures
        animation_continuous(advance_animation(state, targets)),
{
    let result = advance_animation(state, targets);
    assert forall|id: nat| result.parameters.contains_key(id)
    implies parameter_continuous(result.parameters[id]) by {
        let param = state.parameters[id];
        let target = if targets.contains_key(id) {
            targets[id]
        } else {
            param.value
        };
        lemma_advance_preserves_continuity(param, target);
    }
}

///  A steady animation is continuous.
pub proof fn lemma_steady_is_continuous(state: AnimationState)
    requires animation_steady(state),
    ensures animation_continuous(state),
{
    assert forall|id: nat| state.parameters.contains_key(id)
    implies parameter_continuous(state.parameters[id]) by {
        let param = state.parameters[id];
        assert(param.value == param.prev_value);
        lemma_abs_diff_self(param.value);
    }
}

///  Lerp at t=0 returns a.
pub proof fn lemma_lerp_at_zero(a: int, b: int, max_t: nat)
    requires max_t > 0,
    ensures lerp(a, b, 0, max_t) == a,
{
}

///  Lerp at t=max_t returns b.
pub proof fn lemma_lerp_at_max(a: int, b: int, max_t: nat)
    requires max_t > 0,
    ensures lerp(a, b, max_t, max_t) == b,
{
    assert(((b - a) * (max_t as int)) / (max_t as int) == b - a)
        by(nonlinear_arith)
        requires max_t > 0nat;
}

///  Consecutive lerp values differ by at most |b - a| / max_t + 1
///  (the +1 accounts for integer rounding).
pub proof fn lemma_lerp_step_bounded(
    a: int,
    b: int,
    t: nat,
    max_t: nat,
)
    requires
        max_t > 0,
        t < max_t,
    ensures
        abs_diff(lerp(a, b, t + 1, max_t), lerp(a, b, t, max_t))
            <= (abs_diff(b, a) as int) / (max_t as int) + 1,
{
    //  lerp(a, b, t+1, max_t) - lerp(a, b, t, max_t)
    //    = (b - a) * (t+1) / max_t - (b - a) * t / max_t
    //    = (b - a) * ((t+1)/max_t - t/max_t)
    //  For integers: |(b-a)*(t+1)/max_t - (b-a)*t/max_t| <= |b-a|/max_t + 1
    let diff = b - a;
    let v1 = a + (diff * ((t + 1) as int)) / (max_t as int);
    let v0 = a + (diff * (t as int)) / (max_t as int);
    //  v1 - v0 = diff*(t+1)/max_t - diff*t/max_t
    assert(abs_diff(v1, v0) <= (abs_diff(b, a) as int) / (max_t as int) + 1)
        by(nonlinear_arith)
        requires
            max_t > 0nat,
            t < max_t,
            v1 == a + (diff * ((t + 1) as int)) / (max_t as int),
            v0 == a + (diff * (t as int)) / (max_t as int),
            diff == b - a;
}

///  The frame counter always increases after advance.
pub proof fn lemma_advance_increments_frame(
    state: AnimationState,
    targets: Map<nat, int>,
)
    ensures
        advance_animation(state, targets).frame == state.frame + 1,
{
}

} //  verus!
