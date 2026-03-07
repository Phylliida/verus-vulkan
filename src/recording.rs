use vstd::prelude::*;
use crate::render_pass::*;
use crate::pipeline::*;
use crate::framebuffer::*;

verus! {

// ── Types ────────────────────────────────────────────────────────────

/// A render pass instance: tracks which render pass and framebuffer are active,
/// and the current subpass index.
pub struct RenderPassInstance {
    /// The render pass being executed.
    pub render_pass_id: nat,
    /// The framebuffer bound for this render pass instance.
    pub framebuffer_id: nat,
    /// The current subpass index within the render pass.
    pub subpass_index: nat,
}

/// The ghost state of a command buffer during recording.
/// Tracks what is currently bound and whether a render pass is active.
pub struct RecordingState {
    /// Currently bound graphics pipeline, if any.
    pub bound_graphics_pipeline: Option<nat>,
    /// Currently bound compute pipeline, if any.
    pub bound_compute_pipeline: Option<nat>,
    /// Currently bound descriptor sets: maps set index → descriptor set id.
    pub bound_descriptor_sets: Map<nat, nat>,
    /// The active render pass instance, if recording inside a render pass.
    pub active_render_pass: Option<RenderPassInstance>,
}

// ── Spec Functions ───────────────────────────────────────────────────

/// A fresh recording state: nothing bound, no active render pass.
pub open spec fn initial_recording_state() -> RecordingState {
    RecordingState {
        bound_graphics_pipeline: None,
        bound_compute_pipeline: None,
        bound_descriptor_sets: Map::empty(),
        active_render_pass: None,
    }
}

/// Ghost update: bind a graphics pipeline.
pub open spec fn bind_graphics_pipeline(
    state: RecordingState,
    pipeline_id: nat,
) -> RecordingState {
    RecordingState {
        bound_graphics_pipeline: Some(pipeline_id),
        ..state
    }
}

/// Ghost update: bind a compute pipeline.
pub open spec fn bind_compute_pipeline(
    state: RecordingState,
    pipeline_id: nat,
) -> RecordingState {
    RecordingState {
        bound_compute_pipeline: Some(pipeline_id),
        ..state
    }
}

/// Ghost update: bind a descriptor set at a given set index.
pub open spec fn bind_descriptor_set(
    state: RecordingState,
    set_index: nat,
    set_id: nat,
) -> RecordingState {
    RecordingState {
        bound_descriptor_sets: state.bound_descriptor_sets.insert(set_index, set_id),
        ..state
    }
}

/// Ghost update: begin a render pass, entering subpass 0.
pub open spec fn begin_render_pass_recording(
    state: RecordingState,
    rp_id: nat,
    fb_id: nat,
) -> RecordingState {
    RecordingState {
        active_render_pass: Some(RenderPassInstance {
            render_pass_id: rp_id,
            framebuffer_id: fb_id,
            subpass_index: 0,
        }),
        ..state
    }
}

/// Ghost update: end the current render pass.
pub open spec fn end_render_pass_recording(
    state: RecordingState,
) -> RecordingState {
    RecordingState {
        active_render_pass: None,
        ..state
    }
}

/// Ghost update: advance to the next subpass.
pub open spec fn next_subpass_recording(
    state: RecordingState,
) -> RecordingState
    recommends state.active_render_pass.is_some(),
{
    let rpi = state.active_render_pass.unwrap();
    RecordingState {
        active_render_pass: Some(RenderPassInstance {
            subpass_index: rpi.subpass_index + 1,
            ..rpi
        }),
        ..state
    }
}

/// Whether a render pass is currently active.
pub open spec fn in_render_pass(state: RecordingState) -> bool {
    state.active_render_pass.is_some()
}

/// A draw call is valid:
/// - A render pass is active.
/// - A graphics pipeline is bound.
/// - The pipeline is compatible with the current subpass of the render pass.
pub open spec fn draw_call_valid(
    state: RecordingState,
    pipeline: GraphicsPipelineState,
    rp: RenderPassState,
) -> bool {
    state.active_render_pass.is_some()
    && state.bound_graphics_pipeline == Some(pipeline.id)
    && pipeline.alive
    && ({
        let rpi = state.active_render_pass.unwrap();
        rpi.render_pass_id == rp.id
        && rpi.subpass_index < rp.subpasses.len()
        && graphics_pipeline_compatible_with_subpass(pipeline, rp, rpi.subpass_index)
    })
}

/// A dispatch call is valid:
/// - No render pass is active.
/// - A compute pipeline is bound and alive.
pub open spec fn dispatch_call_valid(
    state: RecordingState,
    pipeline: ComputePipelineState,
) -> bool {
    !in_render_pass(state)
    && state.bound_compute_pipeline == Some(pipeline.id)
    && pipeline.alive
}

/// All descriptor set indices required by the pipeline layout are bound.
pub open spec fn descriptor_sets_bound_for_pipeline(
    state: RecordingState,
    pipeline_layouts: Seq<nat>,
) -> bool {
    forall|i: int| 0 <= i < pipeline_layouts.len() ==>
        #[trigger] state.bound_descriptor_sets.contains_key(i as nat)
}

// ── Lemmas ───────────────────────────────────────────────────────────

/// The initial recording state is not in a render pass.
pub proof fn lemma_initial_not_in_render_pass()
    ensures !in_render_pass(initial_recording_state()),
{
}

/// Beginning and then ending a render pass restores not-in-render-pass.
pub proof fn lemma_begin_end_render_pass(
    state: RecordingState,
    rp_id: nat,
    fb_id: nat,
)
    ensures
        !in_render_pass(
            end_render_pass_recording(
                begin_render_pass_recording(state, rp_id, fb_id)
            )
        ),
{
}

/// A valid draw call implies we are in a render pass.
pub proof fn lemma_draw_requires_render_pass(
    state: RecordingState,
    pipeline: GraphicsPipelineState,
    rp: RenderPassState,
)
    requires draw_call_valid(state, pipeline, rp),
    ensures in_render_pass(state),
{
}

/// A valid dispatch call implies we are NOT in a render pass.
pub proof fn lemma_dispatch_requires_no_render_pass(
    state: RecordingState,
    pipeline: ComputePipelineState,
)
    requires dispatch_call_valid(state, pipeline),
    ensures !in_render_pass(state),
{
}

/// Binding a graphics pipeline does not change the render pass state.
pub proof fn lemma_bind_pipeline_preserves_render_pass(
    state: RecordingState,
    id: nat,
)
    ensures
        in_render_pass(bind_graphics_pipeline(state, id)) == in_render_pass(state),
        bind_graphics_pipeline(state, id).active_render_pass == state.active_render_pass,
{
}

} // verus!
