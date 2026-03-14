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
    /// Currently bound descriptor set layouts: maps set index → layout id.
    /// Tracked alongside bound_descriptor_sets so draw/dispatch can verify
    /// that bound sets have layouts matching the pipeline's expected layouts.
    pub bound_set_layouts: Map<nat, nat>,
    /// The active render pass instance, if recording inside a render pass.
    pub active_render_pass: Option<RenderPassInstance>,
    /// Currently bound vertex buffers: maps binding slot → buffer id.
    pub bound_vertex_buffers: Map<nat, nat>,
    /// Currently bound index buffer, if any.
    pub bound_index_buffer: Option<nat>,
    /// Whether the dynamic viewport has been set.
    pub viewport_set: bool,
    /// Whether the dynamic scissor has been set.
    pub scissor_set: bool,
    /// Whether push constants have been set.
    pub push_constants_set: bool,
    /// Dynamic offsets for each descriptor set index: maps set_index → dynamic offsets seq.
    pub bound_dynamic_offsets: Map<nat, Seq<nat>>,
    /// Set layouts of the currently bound graphics pipeline, if any.
    /// Used to invalidate incompatible descriptor sets on pipeline rebind.
    pub bound_graphics_layout: Option<Seq<nat>>,
    /// Set layouts of the currently bound compute pipeline, if any.
    pub bound_compute_layout: Option<Seq<nat>>,
}

// ── Spec Functions ───────────────────────────────────────────────────

/// A fresh recording state: nothing bound, no active render pass.
pub open spec fn initial_recording_state() -> RecordingState {
    RecordingState {
        bound_graphics_pipeline: None,
        bound_compute_pipeline: None,
        bound_descriptor_sets: Map::empty(),
        bound_set_layouts: Map::empty(),
        active_render_pass: None,
        bound_vertex_buffers: Map::empty(),
        bound_index_buffer: None,
        viewport_set: false,
        scissor_set: false,
        push_constants_set: false,
        bound_dynamic_offsets: Map::empty(),
        bound_graphics_layout: None,
        bound_compute_layout: None,
    }
}

/// Find the length of the compatible prefix between two pipeline layouts.
/// Sets at indices < this value have matching set layouts; sets at or above
/// this index are incompatible and must be invalidated (Vulkan spec 14.2.2).
pub open spec fn compatible_prefix_len(
    old_layouts: Seq<nat>,
    new_layouts: Seq<nat>,
) -> nat
    decreases old_layouts.len(),
{
    compatible_prefix_len_rec(old_layouts, new_layouts, 0)
}

/// Recursive helper: find first index >= start where layouts diverge.
pub open spec fn compatible_prefix_len_rec(
    old_layouts: Seq<nat>,
    new_layouts: Seq<nat>,
    start: nat,
) -> nat
    decreases old_layouts.len() - start,
{
    if start >= old_layouts.len() || start >= new_layouts.len() {
        start
    } else if old_layouts[start as int] != new_layouts[start as int] {
        start
    } else {
        compatible_prefix_len_rec(old_layouts, new_layouts, start + 1)
    }
}

/// Invalidate descriptor sets at indices >= the compatible prefix.
/// Vulkan spec 14.2.2: on pipeline rebind, sets whose layout doesn't match
/// the new pipeline's layout at that index are disturbed.
pub open spec fn invalidate_incompatible_sets(
    sets: Map<nat, nat>,
    layouts: Map<nat, nat>,
    offsets: Map<nat, Seq<nat>>,
    old_pipeline_layouts: Option<Seq<nat>>,
    new_pipeline_layouts: Seq<nat>,
) -> (Map<nat, nat>, Map<nat, nat>, Map<nat, Seq<nat>>) {
    match old_pipeline_layouts {
        None => {
            // No previous pipeline: invalidate all sets
            (Map::empty(), Map::empty(), Map::empty())
        },
        Some(old_layouts) => {
            let prefix = compatible_prefix_len(old_layouts, new_pipeline_layouts);
            // Keep only sets at indices < prefix
            (
                Map::new(
                    |k: nat| sets.contains_key(k) && k < prefix,
                    |k: nat| sets[k],
                ),
                Map::new(
                    |k: nat| layouts.contains_key(k) && k < prefix,
                    |k: nat| layouts[k],
                ),
                Map::new(
                    |k: nat| offsets.contains_key(k) && k < prefix,
                    |k: nat| offsets[k],
                ),
            )
        },
    }
}

/// Ghost update: bind a graphics pipeline. Invalidates descriptor sets
/// at indices incompatible with the new pipeline's layout (Vulkan 14.2.2).
pub open spec fn bind_graphics_pipeline(
    state: RecordingState,
    pipeline_id: nat,
    pipeline_layouts: Seq<nat>,
) -> RecordingState {
    let (new_sets, new_layouts, new_offsets) = invalidate_incompatible_sets(
        state.bound_descriptor_sets,
        state.bound_set_layouts,
        state.bound_dynamic_offsets,
        state.bound_graphics_layout,
        pipeline_layouts,
    );
    RecordingState {
        bound_graphics_pipeline: Some(pipeline_id),
        bound_descriptor_sets: new_sets,
        bound_set_layouts: new_layouts,
        bound_dynamic_offsets: new_offsets,
        bound_graphics_layout: Some(pipeline_layouts),
        ..state
    }
}

/// Ghost update: bind a compute pipeline. Invalidates descriptor sets
/// at indices incompatible with the new pipeline's layout (Vulkan 14.2.2).
pub open spec fn bind_compute_pipeline(
    state: RecordingState,
    pipeline_id: nat,
    pipeline_layouts: Seq<nat>,
) -> RecordingState {
    let (new_sets, new_layouts, new_offsets) = invalidate_incompatible_sets(
        state.bound_descriptor_sets,
        state.bound_set_layouts,
        state.bound_dynamic_offsets,
        state.bound_compute_layout,
        pipeline_layouts,
    );
    RecordingState {
        bound_compute_pipeline: Some(pipeline_id),
        bound_descriptor_sets: new_sets,
        bound_set_layouts: new_layouts,
        bound_dynamic_offsets: new_offsets,
        bound_compute_layout: Some(pipeline_layouts),
        ..state
    }
}

/// Ghost update: bind a descriptor set at a given set index.
/// Tracks both the set id and the set's layout id for pipeline compatibility checking.
/// Dynamic offsets are stored for later validation against buffer bounds.
pub open spec fn bind_descriptor_set(
    state: RecordingState,
    set_index: nat,
    set_id: nat,
    layout_id: nat,
    dynamic_offsets: Seq<nat>,
) -> RecordingState {
    RecordingState {
        bound_descriptor_sets: state.bound_descriptor_sets.insert(set_index, set_id),
        bound_set_layouts: state.bound_set_layouts.insert(set_index, layout_id),
        bound_dynamic_offsets: state.bound_dynamic_offsets.insert(set_index, dynamic_offsets),
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

/// All descriptor set indices required by the pipeline layout are bound,
/// and their layout ids match what the pipeline expects.
pub open spec fn descriptor_sets_bound_for_pipeline(
    state: RecordingState,
    pipeline_layouts: Seq<nat>,
) -> bool {
    forall|i: int| 0 <= i < pipeline_layouts.len() ==> (
        #[trigger] state.bound_descriptor_sets.contains_key(i as nat)
        && state.bound_set_layouts.contains_key(i as nat)
        && state.bound_set_layouts[i as nat] == pipeline_layouts[i]
    )
}

// ── Vertex/Index Buffer, Dynamic State, Push Constants ───────────────

/// Ghost update: bind a vertex buffer at a given slot.
pub open spec fn bind_vertex_buffer(
    state: RecordingState,
    slot: nat,
    buffer_id: nat,
) -> RecordingState {
    RecordingState {
        bound_vertex_buffers: state.bound_vertex_buffers.insert(slot, buffer_id),
        ..state
    }
}

/// Ghost update: bind an index buffer.
pub open spec fn bind_index_buffer(
    state: RecordingState,
    buffer_id: nat,
) -> RecordingState {
    RecordingState {
        bound_index_buffer: Some(buffer_id),
        ..state
    }
}

/// Ghost update: set the dynamic viewport.
pub open spec fn set_viewport_recording(state: RecordingState) -> RecordingState {
    RecordingState {
        viewport_set: true,
        ..state
    }
}

/// Ghost update: set the dynamic scissor.
pub open spec fn set_scissor_recording(state: RecordingState) -> RecordingState {
    RecordingState {
        scissor_set: true,
        ..state
    }
}

/// Ghost update: set push constants.
pub open spec fn set_push_constants_recording(state: RecordingState) -> RecordingState {
    RecordingState {
        push_constants_set: true,
        ..state
    }
}

/// At least one vertex buffer is bound (for non-indexed draw).
pub open spec fn has_vertex_buffer_bound(state: RecordingState) -> bool {
    state.bound_vertex_buffers.dom().len() > 0
}

/// An index buffer is bound (for indexed draw).
pub open spec fn has_index_buffer_bound(state: RecordingState) -> bool {
    state.bound_index_buffer.is_some()
}

/// Dynamic state required by the pipeline is satisfied.
/// needs_dynamic_viewport/scissor come from the pipeline's dynamic state flags.
pub open spec fn dynamic_state_satisfied(
    state: RecordingState,
    needs_dynamic_viewport: bool,
    needs_dynamic_scissor: bool,
) -> bool {
    (!needs_dynamic_viewport || state.viewport_set)
    && (!needs_dynamic_scissor || state.scissor_set)
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
    layouts: Seq<nat>,
)
    ensures
        in_render_pass(bind_graphics_pipeline(state, id, layouts)) == in_render_pass(state),
        bind_graphics_pipeline(state, id, layouts).active_render_pass == state.active_render_pass,
{
}

/// Binding a compute pipeline does not change the render pass state.
pub proof fn lemma_bind_compute_preserves_render_pass(
    state: RecordingState, id: nat, layouts: Seq<nat>,
)
    ensures
        in_render_pass(bind_compute_pipeline(state, id, layouts)) == in_render_pass(state),
        bind_compute_pipeline(state, id, layouts).active_render_pass == state.active_render_pass,
{
}

/// Binding a descriptor set does not change the render pass state.
pub proof fn lemma_bind_descriptor_preserves_render_pass(
    state: RecordingState, set_index: nat, set_id: nat, layout_id: nat, dynamic_offsets: Seq<nat>,
)
    ensures
        in_render_pass(bind_descriptor_set(state, set_index, set_id, layout_id, dynamic_offsets)) == in_render_pass(state),
{
}

/// After beginning a render pass, we are in a render pass.
pub proof fn lemma_begin_render_pass_active(
    state: RecordingState, rp_id: nat, fb_id: nat,
)
    ensures in_render_pass(begin_render_pass_recording(state, rp_id, fb_id)),
{
}

/// After ending a render pass, we are NOT in a render pass.
pub proof fn lemma_end_render_pass_inactive(state: RecordingState)
    ensures !in_render_pass(end_render_pass_recording(state)),
{
}

/// Binding a graphics pipeline with no previously bound layout invalidates all descriptors.
pub proof fn lemma_bind_graphics_invalidates_all_when_none(
    state: RecordingState, pipeline_id: nat, layouts: Seq<nat>,
)
    requires
        state.bound_graphics_layout.is_none(),
    ensures
        bind_graphics_pipeline(state, pipeline_id, layouts)
            .bound_descriptor_sets == Map::<nat, nat>::empty(),
{
}

/// The compatible prefix length is always >= start.
proof fn lemma_compatible_prefix_len_rec_lower_bound(
    old_layouts: Seq<nat>,
    new_layouts: Seq<nat>,
    start: nat,
)
    ensures
        compatible_prefix_len_rec(old_layouts, new_layouts, start) >= start,
    decreases old_layouts.len() - start,
{
    if start >= old_layouts.len() || start >= new_layouts.len() {
        // Returns start
    } else if old_layouts[start as int] != new_layouts[start as int] {
        // Returns start
    } else {
        lemma_compatible_prefix_len_rec_lower_bound(old_layouts, new_layouts, start + 1);
    }
}

/// Compatible prefix length is at least as large as the index when layouts match.
proof fn lemma_compatible_prefix_len_rec_ge(
    old_layouts: Seq<nat>,
    new_layouts: Seq<nat>,
    start: nat,
    idx: nat,
)
    requires
        start <= idx,
        idx < old_layouts.len(),
        idx < new_layouts.len(),
        forall|k: int| start <= k <= idx as int ==> old_layouts[k] == new_layouts[k],
    ensures
        compatible_prefix_len_rec(old_layouts, new_layouts, start) > idx,
    decreases idx - start,
{
    // old_layouts[start] == new_layouts[start], so compatible_prefix_len_rec recurses
    assert(old_layouts[start as int] == new_layouts[start as int]);
    if start == idx {
        // After matching at start, compatible_prefix_len_rec recurses to start+1.
        // We need: compatible_prefix_len_rec(_, _, start+1) >= start+1 > idx
        lemma_compatible_prefix_len_rec_lower_bound(old_layouts, new_layouts, start + 1);
    } else {
        // start < idx: recurse on start+1
        lemma_compatible_prefix_len_rec_ge(old_layouts, new_layouts, start + 1, idx);
    }
}

/// Binding a graphics pipeline with the same layouts preserves compatible
/// descriptor sets (sets at indices within the compatible prefix are kept).
pub proof fn lemma_bind_graphics_preserves_compatible_descriptors(
    state: RecordingState, pipeline_id: nat, layouts: Seq<nat>,
    set_idx: nat,
)
    requires
        state.bound_graphics_layout == Some(layouts),
        state.bound_descriptor_sets.contains_key(set_idx),
        set_idx < layouts.len(),
    ensures
        bind_graphics_pipeline(state, pipeline_id, layouts)
            .bound_descriptor_sets.contains_key(set_idx),
        bind_graphics_pipeline(state, pipeline_id, layouts)
            .bound_descriptor_sets[set_idx] == state.bound_descriptor_sets[set_idx],
{
    // When old == new layouts, every index matches, so prefix >= layouts.len()
    lemma_compatible_prefix_len_rec_ge(layouts, layouts, 0, set_idx);
}

/// Beginning a render pass preserves bound pipelines and descriptors.
pub proof fn lemma_begin_rp_preserves_bindings(
    state: RecordingState, rp_id: nat, fb_id: nat,
)
    ensures ({
        let new_state = begin_render_pass_recording(state, rp_id, fb_id);
        new_state.bound_graphics_pipeline == state.bound_graphics_pipeline
        && new_state.bound_compute_pipeline == state.bound_compute_pipeline
        && new_state.bound_descriptor_sets == state.bound_descriptor_sets
        && new_state.bound_set_layouts == state.bound_set_layouts
    }),
{
}

/// Next subpass preserves bound pipelines and descriptors.
pub proof fn lemma_next_subpass_preserves_bindings(state: RecordingState)
    requires state.active_render_pass.is_some(),
    ensures ({
        let new_state = next_subpass_recording(state);
        new_state.bound_graphics_pipeline == state.bound_graphics_pipeline
        && new_state.bound_compute_pipeline == state.bound_compute_pipeline
        && new_state.bound_descriptor_sets == state.bound_descriptor_sets
        && new_state.bound_set_layouts == state.bound_set_layouts
    }),
{
}

/// Binding a vertex buffer preserves the render pass state.
pub proof fn lemma_bind_vertex_preserves_render_pass(
    state: RecordingState, slot: nat, buffer_id: nat,
)
    ensures
        in_render_pass(bind_vertex_buffer(state, slot, buffer_id)) == in_render_pass(state),
{
}

/// Binding an index buffer preserves the render pass state.
pub proof fn lemma_bind_index_preserves_render_pass(
    state: RecordingState, buffer_id: nat,
)
    ensures
        in_render_pass(bind_index_buffer(state, buffer_id)) == in_render_pass(state),
{
}

/// Setting viewport preserves the render pass state.
pub proof fn lemma_set_viewport_preserves_render_pass(state: RecordingState)
    ensures in_render_pass(set_viewport_recording(state)) == in_render_pass(state),
{
}

/// Setting scissor preserves the render pass state.
pub proof fn lemma_set_scissor_preserves_render_pass(state: RecordingState)
    ensures in_render_pass(set_scissor_recording(state)) == in_render_pass(state),
{
}

/// Setting push constants preserves the render pass state.
pub proof fn lemma_set_push_constants_preserves_render_pass(state: RecordingState)
    ensures in_render_pass(set_push_constants_recording(state)) == in_render_pass(state),
{
}

/// Draw and dispatch are mutually exclusive contexts.
pub proof fn lemma_draw_dispatch_exclusive(
    state: RecordingState,
    g_pipeline: GraphicsPipelineState,
    rp: RenderPassState,
    c_pipeline: ComputePipelineState,
)
    ensures !(draw_call_valid(state, g_pipeline, rp) && dispatch_call_valid(state, c_pipeline)),
{
}

} // verus!
