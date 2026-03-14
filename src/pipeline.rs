use vstd::prelude::*;
use crate::render_pass::*;
use crate::descriptor::*;

verus! {

// ── Pipeline Types ────────────────────────────────────────────────────

/// Which bind point a pipeline is bound to.
pub enum PipelineBindPoint {
    Graphics,
    Compute,
}

/// Kinds of dynamic state that can be declared by a pipeline.
pub enum DynamicStateKind {
    Viewport,
    Scissor,
    LineWidth,
    DepthBias,
    BlendConstants,
    DepthBounds,
    StencilCompareMask,
    StencilWriteMask,
    StencilReference,
    // VK_EXT_extended_dynamic_state (Vulkan 1.3)
    CullMode,
    FrontFace,
    PrimitiveTopology,
    DepthTestEnable,
    DepthWriteEnable,
    DepthCompareOp,
    DepthBoundsTestEnable,
    StencilTestEnable,
    StencilOp,
    RasterizerDiscardEnable,
}

/// The state of a graphics pipeline object.
pub struct GraphicsPipelineState {
    pub id: nat,
    /// The render pass this pipeline was created for.
    pub render_pass_id: nat,
    /// The subpass index within that render pass.
    pub subpass_index: nat,
    /// Descriptor set layout IDs this pipeline expects (in set order).
    pub descriptor_set_layouts: Seq<nat>,
    /// Number of color attachments this pipeline writes.
    pub color_attachment_count: nat,
    /// Whether this pipeline has a depth attachment.
    pub has_depth_attachment: bool,
    /// Whether this pipeline is alive (not destroyed).
    pub alive: bool,
    /// Which dynamic states the pipeline declared (must be set before draw).
    pub required_dynamic_states: Set<DynamicStateKind>,
}

/// The state of a compute pipeline object.
pub struct ComputePipelineState {
    pub id: nat,
    /// Descriptor set layout IDs this pipeline expects (in set order).
    pub descriptor_set_layouts: Seq<nat>,
    /// Whether this pipeline is alive (not destroyed).
    pub alive: bool,
}

// ── Spec Functions ────────────────────────────────────────────────────

/// A graphics pipeline is compatible with a specific subpass of a render pass:
/// matching render pass id, subpass index, and attachment expectations.
pub open spec fn graphics_pipeline_compatible_with_subpass(
    pipeline: GraphicsPipelineState,
    rp: RenderPassState,
    s: nat,
) -> bool
    recommends s < rp.subpasses.len(),
{
    pipeline.render_pass_id == rp.id
    && pipeline.subpass_index == s
    && pipeline.color_attachment_count == subpass_color_attachment_count(rp, s)
    && pipeline.has_depth_attachment == subpass_has_depth(rp, s)
}

/// A pipeline's descriptor set layouts are compatible with the currently
/// bound descriptor set layout IDs.  The bound layouts must be a prefix
/// (or exact match) of the pipeline's expected layouts.
pub open spec fn pipeline_descriptor_layout_compatible(
    pipeline_layouts: Seq<nat>,
    bound_layouts: Seq<nat>,
) -> bool {
    pipeline_layouts.len() <= bound_layouts.len()
    && (forall|i: int| 0 <= i < pipeline_layouts.len() ==>
        pipeline_layouts[i] == bound_layouts[i])
}

/// A graphics pipeline is well-formed with respect to a render pass.
pub open spec fn graphics_pipeline_well_formed(
    pipeline: GraphicsPipelineState,
    rp: RenderPassState,
) -> bool {
    pipeline.alive
    && pipeline.subpass_index < rp.subpasses.len()
    && pipeline.color_attachment_count == subpass_color_attachment_count(rp, pipeline.subpass_index)
    && pipeline.has_depth_attachment == subpass_has_depth(rp, pipeline.subpass_index)
}

/// A compute pipeline is well-formed.
pub open spec fn compute_pipeline_well_formed(
    pipeline: ComputePipelineState,
) -> bool {
    pipeline.alive
}

/// Ghost update: destroy a graphics pipeline.
pub open spec fn destroy_graphics_pipeline_ghost(
    pipeline: GraphicsPipelineState,
) -> GraphicsPipelineState
    recommends pipeline.alive,
{
    GraphicsPipelineState {
        alive: false,
        ..pipeline
    }
}

/// Ghost update: destroy a compute pipeline.
pub open spec fn destroy_compute_pipeline_ghost(
    pipeline: ComputePipelineState,
) -> ComputePipelineState
    recommends pipeline.alive,
{
    ComputePipelineState {
        alive: false,
        ..pipeline
    }
}

// ── Lemmas ────────────────────────────────────────────────────────────

/// A compatible graphics pipeline has the correct color attachment count.
pub proof fn lemma_compatible_matches_colors(
    pipeline: GraphicsPipelineState,
    rp: RenderPassState,
    s: nat,
)
    requires
        graphics_pipeline_compatible_with_subpass(pipeline, rp, s),
        s < rp.subpasses.len(),
    ensures
        pipeline.color_attachment_count == subpass_color_attachment_count(rp, s),
{
}

/// A compatible graphics pipeline has the correct depth flag.
pub proof fn lemma_compatible_matches_depth(
    pipeline: GraphicsPipelineState,
    rp: RenderPassState,
    s: nat,
)
    requires
        graphics_pipeline_compatible_with_subpass(pipeline, rp, s),
        s < rp.subpasses.len(),
    ensures
        pipeline.has_depth_attachment == subpass_has_depth(rp, s),
{
}

/// A descriptor layout sequence is compatible with itself.
pub proof fn lemma_descriptor_layout_compatible_reflexive(
    layouts: Seq<nat>,
)
    ensures
        pipeline_descriptor_layout_compatible(layouts, layouts),
{
}

/// A well-formed graphics pipeline is alive.
pub proof fn lemma_graphics_well_formed_is_alive(
    pipeline: GraphicsPipelineState, rp: RenderPassState,
)
    requires graphics_pipeline_well_formed(pipeline, rp),
    ensures pipeline.alive,
{
}

/// A well-formed compute pipeline is alive.
pub proof fn lemma_compute_well_formed_is_alive(pipeline: ComputePipelineState)
    requires compute_pipeline_well_formed(pipeline),
    ensures pipeline.alive,
{
}

/// Compatible pipeline implies well-formed.
pub proof fn lemma_compatible_implies_well_formed(
    pipeline: GraphicsPipelineState, rp: RenderPassState, s: nat,
)
    requires
        graphics_pipeline_compatible_with_subpass(pipeline, rp, s),
        pipeline.alive,
        s < rp.subpasses.len(),
    ensures graphics_pipeline_well_formed(pipeline, rp),
{
}

/// Descriptor layout compatibility is transitive on prefix.
pub proof fn lemma_descriptor_layout_prefix_transitive(
    a: Seq<nat>, b: Seq<nat>, c: Seq<nat>,
)
    requires
        pipeline_descriptor_layout_compatible(a, b),
        pipeline_descriptor_layout_compatible(b, c),
    ensures
        pipeline_descriptor_layout_compatible(a, c),
{
    assert forall|i: int| 0 <= i < a.len() implies a[i] == c[i] by {
        assert(a[i] == b[i]);
        assert(b[i] == c[i]);
    }
}

/// After destroying, a graphics pipeline is not alive.
/// Caller must prove the pipeline is alive before destroying.
pub proof fn lemma_destroy_graphics_pipeline_not_alive(
    pipeline: GraphicsPipelineState,
)
    requires pipeline.alive,
    ensures !destroy_graphics_pipeline_ghost(pipeline).alive,
{
}

/// After destroying, a compute pipeline is not alive.
/// Caller must prove the pipeline is alive before destroying.
pub proof fn lemma_destroy_compute_pipeline_not_alive(
    pipeline: ComputePipelineState,
)
    requires pipeline.alive,
    ensures !destroy_compute_pipeline_ghost(pipeline).alive,
{
}

/// Destroying a graphics pipeline preserves its id.
pub proof fn lemma_destroy_graphics_pipeline_preserves_id(
    pipeline: GraphicsPipelineState,
)
    ensures destroy_graphics_pipeline_ghost(pipeline).id == pipeline.id,
{
}

/// Destroying a compute pipeline preserves its id.
pub proof fn lemma_destroy_compute_pipeline_preserves_id(
    pipeline: ComputePipelineState,
)
    ensures destroy_compute_pipeline_ghost(pipeline).id == pipeline.id,
{
}

} // verus!
