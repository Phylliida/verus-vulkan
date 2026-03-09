use vstd::prelude::*;
use crate::pipeline::*;
use crate::pipeline_layout::*;
use crate::lifetime::*;
use crate::sync_token::*;
use super::device::RuntimeDevice;

verus! {

/// Runtime wrapper for a graphics pipeline.
pub struct RuntimeGraphicsPipeline {
    /// Opaque handle (maps to VkPipeline).
    pub handle: u64,
    /// Ghost model of the pipeline state.
    pub state: Ghost<GraphicsPipelineState>,
}

impl View for RuntimeGraphicsPipeline {
    type V = GraphicsPipelineState;
    open spec fn view(&self) -> GraphicsPipelineState { self.state@ }
}

/// Runtime wrapper for a compute pipeline.
pub struct RuntimeComputePipeline {
    /// Opaque handle (maps to VkPipeline).
    pub handle: u64,
    /// Ghost model of the pipeline state.
    pub state: Ghost<ComputePipelineState>,
}

impl View for RuntimeComputePipeline {
    type V = ComputePipelineState;
    open spec fn view(&self) -> ComputePipelineState { self.state@ }
}

/// Well-formedness of the runtime graphics pipeline (alive).
pub open spec fn runtime_gfx_pipeline_wf(
    pipe: &RuntimeGraphicsPipeline,
) -> bool {
    pipe@.alive
}

/// Well-formedness of the runtime compute pipeline.
pub open spec fn runtime_compute_pipeline_wf(
    pipe: &RuntimeComputePipeline,
) -> bool {
    compute_pipeline_well_formed(pipe@)
}

/// Exec: create a graphics pipeline.
pub fn create_graphics_pipeline_exec(
    gps: Ghost<GraphicsPipelineState>,
) -> (out: RuntimeGraphicsPipeline)
    requires gps@.alive,
    ensures
        out@ == gps@,
        runtime_gfx_pipeline_wf(&out),
{
    RuntimeGraphicsPipeline {
        handle: 0,
        state: gps,
    }
}

/// Exec: create a compute pipeline.
pub fn create_compute_pipeline_exec(
    cps: Ghost<ComputePipelineState>,
) -> (out: RuntimeComputePipeline)
    requires compute_pipeline_well_formed(cps@),
    ensures
        out@ == cps@,
        runtime_compute_pipeline_wf(&out),
{
    RuntimeComputePipeline {
        handle: 0,
        state: cps,
    }
}

/// Exec: destroy a graphics pipeline (sets alive to false in ghost state).
/// Caller must prove the pipeline is not currently bound in any active recording
/// and holds exclusive access.
pub fn destroy_graphics_pipeline_exec(
    pipe: &mut RuntimeGraphicsPipeline,
    dev: &RuntimeDevice,
    thread: Ghost<ThreadId>,
    reg: Ghost<TokenRegistry>,
)
    requires
        runtime_gfx_pipeline_wf(&*old(pipe)),
        // All pending submissions must be completed (pipeline may be referenced by any CB)
        forall|i: int| 0 <= i < dev@.pending_submissions.len()
            ==> (#[trigger] dev@.pending_submissions[i]).completed,
        holds_exclusive(reg@, old(pipe)@.id, thread@),
    ensures
        !pipe@.alive,
        pipe@.id == old(pipe)@.id,
{
    pipe.state = Ghost(GraphicsPipelineState {
        alive: false,
        ..pipe.state@
    });
}

/// Exec: destroy a compute pipeline.
/// Caller must prove the pipeline is not currently bound in any active recording
/// and holds exclusive access.
pub fn destroy_compute_pipeline_exec(
    pipe: &mut RuntimeComputePipeline,
    dev: &RuntimeDevice,
    thread: Ghost<ThreadId>,
    reg: Ghost<TokenRegistry>,
)
    requires
        runtime_compute_pipeline_wf(&*old(pipe)),
        // All pending submissions must be completed (pipeline may be referenced by any CB)
        forall|i: int| 0 <= i < dev@.pending_submissions.len()
            ==> (#[trigger] dev@.pending_submissions[i]).completed,
        holds_exclusive(reg@, old(pipe)@.id, thread@),
    ensures
        !pipe@.alive,
        pipe@.id == old(pipe)@.id,
{
    pipe.state = Ghost(ComputePipelineState {
        alive: false,
        ..pipe.state@
    });
}

// ── Extended Specs & Proofs ──────────────────────────────────────────

/// Graphics pipeline is alive.
pub open spec fn gfx_pipeline_alive(pipe: &RuntimeGraphicsPipeline) -> bool {
    pipe@.alive
}

/// Compute pipeline is alive.
pub open spec fn compute_pipeline_alive(pipe: &RuntimeComputePipeline) -> bool {
    pipe@.alive
}

/// Graphics pipeline ID.
pub open spec fn gfx_pipeline_id(pipe: &RuntimeGraphicsPipeline) -> nat {
    pipe@.id
}

/// Compute pipeline ID.
pub open spec fn compute_pipeline_id(pipe: &RuntimeComputePipeline) -> nat {
    pipe@.id
}

/// Proof: creating a graphics pipeline produces an alive pipeline.
pub proof fn lemma_create_gfx_alive(gps: Ghost<GraphicsPipelineState>)
    requires gps@.alive,
    ensures gfx_pipeline_alive(&RuntimeGraphicsPipeline {
        handle: 0,
        state: gps,
    }),
{
}

/// Proof: creating a compute pipeline produces an alive pipeline.
pub proof fn lemma_create_compute_alive(cps: Ghost<ComputePipelineState>)
    requires compute_pipeline_well_formed(cps@),
    ensures compute_pipeline_alive(&RuntimeComputePipeline {
        handle: 0,
        state: cps,
    }),
{
}

/// Proof: destroying a graphics pipeline preserves its ID.
pub proof fn lemma_destroy_gfx_preserves_id(pipe: &RuntimeGraphicsPipeline)
    requires runtime_gfx_pipeline_wf(pipe),
    ensures ({
        let destroyed = GraphicsPipelineState { alive: false, ..pipe@ };
        destroyed.id == pipe@.id
    }),
{
}

/// Proof: destroying a compute pipeline preserves its ID.
pub proof fn lemma_destroy_compute_preserves_id(pipe: &RuntimeComputePipeline)
    requires runtime_compute_pipeline_wf(pipe),
    ensures ({
        let destroyed = ComputePipelineState { alive: false, ..pipe@ };
        destroyed.id == pipe@.id
    }),
{
}

// ── Pipeline Layout Runtime ─────────────────────────────────────────

/// Runtime wrapper for a Vulkan pipeline layout.
pub struct RuntimePipelineLayout {
    /// Opaque handle (maps to VkPipelineLayout).
    pub handle: u64,
    /// Ghost model of the pipeline layout state.
    pub state: Ghost<PipelineLayoutState>,
}

impl View for RuntimePipelineLayout {
    type V = PipelineLayoutState;
    open spec fn view(&self) -> PipelineLayoutState { self.state@ }
}

/// Well-formedness of the runtime pipeline layout.
pub open spec fn runtime_pipeline_layout_wf(
    layout: &RuntimePipelineLayout,
) -> bool {
    pipeline_layout_well_formed(layout@)
}

/// Exec: create a pipeline layout.
pub fn create_pipeline_layout_exec(
    pls: Ghost<PipelineLayoutState>,
) -> (out: RuntimePipelineLayout)
    requires pipeline_layout_well_formed(pls@),
    ensures
        out@ == pls@,
        runtime_pipeline_layout_wf(&out),
{
    RuntimePipelineLayout {
        handle: 0,
        state: pls,
    }
}

/// Exec: destroy a pipeline layout.
pub fn destroy_pipeline_layout_exec(
    layout: &mut RuntimePipelineLayout,
    dev: &RuntimeDevice,
    thread: Ghost<ThreadId>,
    reg: Ghost<TokenRegistry>,
)
    requires
        runtime_pipeline_layout_wf(&*old(layout)),
        forall|i: int| 0 <= i < dev@.pending_submissions.len()
            ==> (#[trigger] dev@.pending_submissions[i]).completed,
        holds_exclusive(reg@, old(layout)@.id, thread@),
    ensures
        !layout@.alive,
        layout@.id == old(layout)@.id,
{
    layout.state = Ghost(PipelineLayoutState {
        alive: false,
        ..layout.state@
    });
}

/// Exec: check if two pipeline layouts are fully compatible.
pub fn check_layout_compatible_exec(
    layout_a: &RuntimePipelineLayout,
    layout_b: &RuntimePipelineLayout,
) -> (result: Ghost<bool>)
    ensures result@ == layouts_fully_compatible(layout_a@, layout_b@),
{
    Ghost(layouts_fully_compatible(layout_a.state@, layout_b.state@))
}

/// Proof: a well-formed pipeline layout is alive.
pub proof fn lemma_create_pipeline_layout_alive(pls: PipelineLayoutState)
    requires pipeline_layout_well_formed(pls),
    ensures pls.alive,
{
}

/// Proof: destroying a pipeline layout preserves its ID.
pub proof fn lemma_destroy_pipeline_layout_preserves_id(layout: PipelineLayoutState)
    requires pipeline_layout_well_formed(layout),
    ensures ({
        let destroyed = PipelineLayoutState { alive: false, ..layout };
        destroyed.id == layout.id
    }),
{
}

} // verus!
