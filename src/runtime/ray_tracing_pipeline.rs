use vstd::prelude::*;
use crate::ray_tracing_pipeline::*;
use crate::lifetime::*;
use crate::sync_token::*;
use super::device::RuntimeDevice;

verus! {

/// Runtime wrapper for a ray tracing pipeline (VkPipeline).
pub struct RuntimeRayTracingPipeline {
    /// Opaque handle (maps to VkPipeline).
    pub handle: u64,
    /// Ghost model of the ray tracing pipeline state.
    pub state: Ghost<RayTracingPipelineState>,
}

impl View for RuntimeRayTracingPipeline {
    type V = RayTracingPipelineState;
    open spec fn view(&self) -> RayTracingPipelineState { self.state@ }
}

/// Well-formedness of the runtime ray tracing pipeline.
pub open spec fn runtime_rt_pipeline_wf(pipe: &RuntimeRayTracingPipeline) -> bool {
    rt_pipeline_well_formed(pipe@)
}

/// Exec: create a ray tracing pipeline from ghost state.
pub fn create_rt_pipeline_exec(
    rt_state: Ghost<RayTracingPipelineState>,
) -> (out: RuntimeRayTracingPipeline)
    requires rt_pipeline_well_formed(rt_state@),
    ensures
        out@ == rt_state@,
        runtime_rt_pipeline_wf(&out),
{
    RuntimeRayTracingPipeline {
        handle: 0,
        state: rt_state,
    }
}

/// Exec: destroy a ray tracing pipeline.
pub fn destroy_rt_pipeline_exec(
    pipe: &mut RuntimeRayTracingPipeline,
    dev: &RuntimeDevice,
    thread: Ghost<ThreadId>,
    reg: Ghost<TokenRegistry>,
)
    requires
        runtime_rt_pipeline_wf(&*old(pipe)),
        forall|i: int| 0 <= i < dev@.pending_submissions.len()
            ==> (#[trigger] dev@.pending_submissions[i]).completed,
        holds_exclusive(reg@, SyncObjectId::Handle(old(pipe)@.id), thread@),
    ensures
        pipe@ == destroy_rt_pipeline_ghost(old(pipe)@),
        !pipe@.alive,
{
    pipe.state = Ghost(destroy_rt_pipeline_ghost(pipe.state@));
}

// ── Specs & Proofs ──────────────────────────────────────────────────

/// Pipeline is alive.
pub open spec fn rt_pipeline_alive(pipe: &RuntimeRayTracingPipeline) -> bool {
    pipe@.alive
}

/// Proof: creating a pipeline produces an alive pipeline.
pub proof fn lemma_create_rt_pipeline_alive(rt_state: Ghost<RayTracingPipelineState>)
    requires rt_pipeline_well_formed(rt_state@),
    ensures rt_pipeline_alive(&RuntimeRayTracingPipeline {
        handle: 0,
        state: rt_state,
    }),
{
}

/// Proof: destroying a pipeline preserves its id.
pub proof fn lemma_destroy_rt_pipeline_preserves_id_rt(pipe: &RuntimeRayTracingPipeline)
    requires runtime_rt_pipeline_wf(pipe),
    ensures destroy_rt_pipeline_ghost(pipe@).id == pipe@.id,
{
}

} // verus!
