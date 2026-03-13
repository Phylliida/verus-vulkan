use vstd::prelude::*;
use crate::animation::*;

verus! {

/// Runtime wrapper for animation state tracking.
pub struct RuntimeAnimation {
    /// Ghost model of the animation state.
    pub state: Ghost<AnimationState>,
}

impl View for RuntimeAnimation {
    type V = AnimationState;
    open spec fn view(&self) -> AnimationState { self.state@ }
}

/// Exec: create an animation tracker from ghost state.
pub fn create_animation_exec(
    anim_state: Ghost<AnimationState>,
) -> (out: RuntimeAnimation)
    ensures out@ == anim_state@,
{
    RuntimeAnimation { state: anim_state }
}

/// Exec: advance all animation parameters toward their targets.
pub fn advance_animation_exec(
    anim: &mut RuntimeAnimation,
    targets: Ghost<Map<nat, int>>,
)
    ensures
        anim@ == advance_animation(old(anim)@, targets@),
        animation_continuous(anim@),
{
    proof { lemma_advance_animation_continuous(anim.state@, targets@); }
    anim.state = Ghost(advance_animation(anim.state@, targets@));
}

} // verus!
