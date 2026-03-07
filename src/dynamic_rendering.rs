use vstd::prelude::*;
use crate::image_layout::*;
use crate::msaa::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// A color attachment for dynamic rendering (VK_KHR_dynamic_rendering).
pub struct DynamicColorAttachment {
    /// Image view id.
    pub image_view: nat,
    /// Current image layout.
    pub image_layout: ImageLayout,
    /// Optional resolve image view.
    pub resolve_image_view: Option<nat>,
    /// Resolve image layout.
    pub resolve_image_layout: ImageLayout,
    /// Sample count.
    pub samples: SampleCount,
}

/// A depth/stencil attachment for dynamic rendering.
pub struct DynamicDepthStencilAttachment {
    pub image_view: nat,
    pub image_layout: ImageLayout,
    pub samples: SampleCount,
}

/// Rendering info for VK_KHR_dynamic_rendering (replaces VkRenderPass + VkFramebuffer).
pub struct DynamicRenderingInfo {
    /// Render area.
    pub render_area_width: nat,
    pub render_area_height: nat,
    /// Color attachments.
    pub color_attachments: Seq<DynamicColorAttachment>,
    /// Optional depth attachment.
    pub depth_attachment: Option<DynamicDepthStencilAttachment>,
    /// Optional stencil attachment.
    pub stencil_attachment: Option<DynamicDepthStencilAttachment>,
    /// Number of layers.
    pub layer_count: nat,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// A color attachment layout is valid for rendering.
pub open spec fn color_attachment_layout_valid(layout: ImageLayout) -> bool {
    layout == ImageLayout::ColorAttachmentOptimal
    || layout == ImageLayout::General
}

/// A depth attachment layout is valid for rendering.
pub open spec fn depth_attachment_layout_valid(layout: ImageLayout) -> bool {
    layout == ImageLayout::DepthStencilAttachmentOptimal
    || layout == ImageLayout::DepthStencilReadOnlyOptimal
    || layout == ImageLayout::General
}

/// All color attachments have valid layouts.
pub open spec fn all_color_layouts_valid(
    info: DynamicRenderingInfo,
) -> bool {
    forall|i: int| 0 <= i < info.color_attachments.len()
        ==> color_attachment_layout_valid(
            (#[trigger] info.color_attachments[i]).image_layout)
}

/// Depth/stencil attachment layout is valid.
pub open spec fn depth_stencil_layout_valid(
    info: DynamicRenderingInfo,
) -> bool {
    (match info.depth_attachment {
        Some(d) => depth_attachment_layout_valid(d.image_layout),
        None => true,
    })
    && (match info.stencil_attachment {
        Some(s) => depth_attachment_layout_valid(s.image_layout),
        None => true,
    })
}

/// Dynamic rendering info is well-formed.
pub open spec fn dynamic_rendering_well_formed(
    info: DynamicRenderingInfo,
) -> bool {
    info.render_area_width > 0
    && info.render_area_height > 0
    && info.layer_count > 0
    && all_color_layouts_valid(info)
    && depth_stencil_layout_valid(info)
}

/// All sample counts in the rendering match.
pub open spec fn dynamic_rendering_samples_match(
    info: DynamicRenderingInfo,
    pipeline_samples: SampleCount,
) -> bool {
    (forall|i: int| 0 <= i < info.color_attachments.len()
        ==> (#[trigger] info.color_attachments[i]).samples == pipeline_samples)
    && (match info.depth_attachment {
        Some(d) => d.samples == pipeline_samples,
        None => true,
    })
}

/// Number of color attachments in the dynamic rendering.
pub open spec fn dynamic_color_attachment_count(
    info: DynamicRenderingInfo,
) -> nat {
    info.color_attachments.len()
}

/// Whether dynamic rendering has a depth attachment.
pub open spec fn dynamic_has_depth(info: DynamicRenderingInfo) -> bool {
    info.depth_attachment.is_some()
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// ColorAttachmentOptimal is a valid color layout.
pub proof fn lemma_color_optimal_valid()
    ensures color_attachment_layout_valid(ImageLayout::ColorAttachmentOptimal),
{
}

/// DepthStencilAttachmentOptimal is a valid depth layout.
pub proof fn lemma_depth_optimal_valid()
    ensures depth_attachment_layout_valid(ImageLayout::DepthStencilAttachmentOptimal),
{
}

/// Undefined is NOT a valid color attachment layout.
pub proof fn lemma_undefined_not_color()
    ensures !color_attachment_layout_valid(ImageLayout::Undefined),
{
}

/// TransferSrcOptimal is NOT a valid color attachment layout.
pub proof fn lemma_transfer_src_not_color()
    ensures !color_attachment_layout_valid(ImageLayout::TransferSrcOptimal),
{
}

/// Empty color attachments are trivially valid.
pub proof fn lemma_empty_colors_valid(info: DynamicRenderingInfo)
    requires info.color_attachments.len() == 0,
    ensures all_color_layouts_valid(info),
{
}

/// No depth/stencil attachment is trivially valid.
pub proof fn lemma_no_depth_stencil_valid(info: DynamicRenderingInfo)
    requires
        info.depth_attachment.is_none(),
        info.stencil_attachment.is_none(),
    ensures depth_stencil_layout_valid(info),
{
}

} // verus!
