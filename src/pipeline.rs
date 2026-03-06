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

} // verus!
