use vstd::prelude::*;
use crate::render_pass::*;

verus! {

// ── Image View ───────────────────────────────────────────────────────

/// The state of a created image view object.
pub struct ImageViewState {
    /// Unique identifier for this image view.
    pub id: nat,
    /// The image this view references.
    pub image_id: nat,
    /// Numeric format identifier.
    pub format: nat,
    /// Whether this image view is alive (not destroyed).
    pub alive: bool,
}

// ── Framebuffer ──────────────────────────────────────────────────────

/// The state of a created framebuffer object.
pub struct FramebufferState {
    /// Unique identifier for this framebuffer.
    pub id: nat,
    /// The render pass this framebuffer is compatible with.
    pub render_pass_id: nat,
    /// Image view IDs for each attachment (ordered to match render pass attachments).
    pub attachments: Seq<nat>,
    /// Framebuffer width in pixels.
    pub width: nat,
    /// Framebuffer height in pixels.
    pub height: nat,
    /// Number of layers.
    pub layers: nat,
    /// Whether this framebuffer is alive (not destroyed).
    pub alive: bool,
}

// ── Spec Functions ───────────────────────────────────────────────────

/// The framebuffer's attachment count matches the render pass's attachment count.
pub open spec fn framebuffer_attachment_count_matches(
    fb: FramebufferState,
    rp: RenderPassState,
) -> bool {
    fb.attachments.len() == rp.attachments.len()
}

/// A framebuffer is well-formed with respect to a render pass:
/// matching render pass id, attachment count, positive dimensions, and alive.
pub open spec fn framebuffer_well_formed(
    fb: FramebufferState,
    rp: RenderPassState,
) -> bool {
    fb.alive
    && fb.render_pass_id == rp.id
    && framebuffer_attachment_count_matches(fb, rp)
    && fb.width > 0
    && fb.height > 0
    && fb.layers > 0
}

/// A framebuffer has valid (positive) dimensions.
pub open spec fn framebuffer_dimensions_valid(fb: FramebufferState) -> bool {
    fb.width > 0 && fb.height > 0 && fb.layers > 0
}

/// An image view is well-formed: it is alive.
pub open spec fn image_view_well_formed(view: ImageViewState) -> bool {
    view.alive
}

/// A framebuffer is compatible with a render pass:
/// matching render pass id and attachment count.
pub open spec fn framebuffer_compatible_with_render_pass(
    fb: FramebufferState,
    rp: RenderPassState,
) -> bool {
    fb.render_pass_id == rp.id
    && framebuffer_attachment_count_matches(fb, rp)
}

// ── Lemmas ───────────────────────────────────────────────────────────

/// A well-formed framebuffer has an attachment count matching the render pass.
pub proof fn lemma_well_formed_attachment_count(
    fb: FramebufferState,
    rp: RenderPassState,
)
    requires framebuffer_well_formed(fb, rp),
    ensures framebuffer_attachment_count_matches(fb, rp),
{
}

/// A well-formed framebuffer has positive dimensions.
pub proof fn lemma_well_formed_dimensions(
    fb: FramebufferState,
    rp: RenderPassState,
)
    requires framebuffer_well_formed(fb, rp),
    ensures framebuffer_dimensions_valid(fb),
{
}

/// A well-formed framebuffer is compatible with its render pass.
pub proof fn lemma_well_formed_implies_compatible(
    fb: FramebufferState,
    rp: RenderPassState,
)
    requires framebuffer_well_formed(fb, rp),
    ensures framebuffer_compatible_with_render_pass(fb, rp),
{
}

/// A well-formed framebuffer is alive.
pub proof fn lemma_well_formed_is_alive(
    fb: FramebufferState, rp: RenderPassState,
)
    requires framebuffer_well_formed(fb, rp),
    ensures fb.alive,
{
}

/// Compatible framebuffer matches the render pass ID.
pub proof fn lemma_compatible_matches_rp_id(
    fb: FramebufferState, rp: RenderPassState,
)
    requires framebuffer_compatible_with_render_pass(fb, rp),
    ensures fb.render_pass_id == rp.id,
{
}

} // verus!
