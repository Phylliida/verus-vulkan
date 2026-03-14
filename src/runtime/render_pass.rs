use vstd::prelude::*;
use crate::lifetime::*;
use crate::render_pass::*;
use crate::sync_token::*;
use super::device::RuntimeDevice;

verus! {

/// Runtime wrapper for a Vulkan render pass.
pub struct RuntimeRenderPass {
    /// Opaque handle (maps to VkRenderPass).
    pub handle: u64,
    /// Ghost model of the render pass state.
    pub state: Ghost<RenderPassState>,
}

impl View for RuntimeRenderPass {
    type V = RenderPassState;
    open spec fn view(&self) -> RenderPassState { self.state@ }
}

/// Well-formedness of the runtime render pass.
pub open spec fn runtime_render_pass_wf(rp: &RuntimeRenderPass) -> bool {
    render_pass_well_formed(rp@) && rp@.alive
}

/// Exec: create a render pass from a ghost state.
pub fn create_render_pass_exec(
    rps: Ghost<RenderPassState>,
) -> (out: RuntimeRenderPass)
    requires render_pass_well_formed(rps@), rps@.alive,
    ensures
        out@ == rps@,
        runtime_render_pass_wf(&out),
{
    RuntimeRenderPass {
        handle: 0,
        state: rps,
    }
}

/// Exec: destroy a render pass.
/// Caller must prove exclusive access.
pub fn destroy_render_pass_exec(
    rp: &mut RuntimeRenderPass,
    dev: &RuntimeDevice,
    thread: Ghost<ThreadId>,
    reg: Ghost<TokenRegistry>,
)
    requires
        runtime_render_pass_wf(&*old(rp)),
        // All pending submissions must be completed
        forall|i: int| 0 <= i < dev@.pending_submissions.len()
            ==> (#[trigger] dev@.pending_submissions[i]).completed,
        holds_exclusive(reg@, SyncObjectId::Handle(old(rp)@.id), thread@),
    ensures
        rp@ == destroy_render_pass_ghost(old(rp)@),
        !rp@.alive,
{
    rp.state = Ghost(destroy_render_pass_ghost(rp.state@));
}

// ── Extended Specs & Proofs ──────────────────────────────────────────

/// Render pass is alive.
pub open spec fn render_pass_alive(rp: &RuntimeRenderPass) -> bool {
    rp@.alive
}

/// Render pass ID.
pub open spec fn render_pass_id(rp: &RuntimeRenderPass) -> nat {
    rp@.id
}

/// Proof: creating a render pass produces an alive pass.
pub proof fn lemma_create_render_pass_alive(rps: Ghost<RenderPassState>)
    requires render_pass_well_formed(rps@), rps@.alive,
    ensures render_pass_alive(&RuntimeRenderPass {
        handle: 0,
        state: rps,
    }),
{
}

/// Proof: destroying a render pass preserves its id.
pub proof fn lemma_destroy_render_pass_preserves_id_rt(rp: &RuntimeRenderPass)
    requires runtime_render_pass_wf(rp),
    ensures destroy_render_pass_ghost(rp@).id == rp@.id,
{
}

/// Proof: a well-formed runtime render pass has at least one subpass.
pub proof fn lemma_runtime_rp_has_subpasses(rp: &RuntimeRenderPass)
    requires runtime_render_pass_wf(rp),
    ensures rp@.subpasses.len() > 0,
{
    lemma_well_formed_has_subpasses(rp@);
}

} // verus!
