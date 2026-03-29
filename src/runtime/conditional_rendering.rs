use vstd::prelude::*;
use crate::conditional_rendering::*;

verus! {

///  Runtime wrapper for conditional rendering state (VK_EXT_conditional_rendering).
pub struct RuntimeConditionalRendering {
    ///  Ghost model of the conditional rendering state.
    pub state: Ghost<ConditionalRenderingState>,
}

impl View for RuntimeConditionalRendering {
    type V = ConditionalRenderingState;
    open spec fn view(&self) -> ConditionalRenderingState { self.state@ }
}

///  Exec: create conditional rendering in the initial (inactive) state.
pub fn create_conditional_rendering_exec() -> (out: RuntimeConditionalRendering)
    ensures
        out@ == no_conditional_rendering(),
        commands_unconditional(out@),
{
    RuntimeConditionalRendering {
        state: Ghost(no_conditional_rendering()),
    }
}

///  Exec: begin conditional rendering.
pub fn begin_conditional_exec(
    cr: &mut RuntimeConditionalRendering,
    buffer_id: Ghost<nat>,
    offset: Ghost<nat>,
    inverted: Ghost<bool>,
)
    requires commands_unconditional(old(cr)@),
    ensures
        cr@ == begin_conditional(buffer_id@, offset@, inverted@),
        command_is_conditional(cr@),
{
    cr.state = Ghost(begin_conditional(buffer_id@, offset@, inverted@));
}

///  Exec: end conditional rendering.
pub fn end_conditional_exec(cr: &mut RuntimeConditionalRendering)
    requires command_is_conditional(old(cr)@),
    ensures
        cr@ == end_conditional(),
        commands_unconditional(cr@),
{
    cr.state = Ghost(end_conditional());
}

} //  verus!
