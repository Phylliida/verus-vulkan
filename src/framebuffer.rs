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
    /// Width of the viewed image (in pixels).
    pub width: nat,
    /// Height of the viewed image (in pixels).
    pub height: nat,
    /// Number of samples (1 = no MSAA, 2/4/8/16/32/64 for MSAA).
    pub samples: nat,
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

// ── Ghost Destroy ───────────────────────────────────────────────────

/// Ghost update: destroy a framebuffer.
pub open spec fn destroy_framebuffer_ghost(
    fb: FramebufferState,
) -> FramebufferState {
    FramebufferState {
        alive: false,
        ..fb
    }
}

/// Ghost update: destroy an image view.
pub open spec fn destroy_image_view_ghost(
    view: ImageViewState,
) -> ImageViewState {
    ImageViewState {
        alive: false,
        ..view
    }
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

/// After destroying, a framebuffer is not alive.
pub proof fn lemma_destroy_framebuffer_not_alive(fb: FramebufferState)
    ensures !destroy_framebuffer_ghost(fb).alive,
{
}

/// After destroying, an image view is not alive.
pub proof fn lemma_destroy_image_view_not_alive(view: ImageViewState)
    ensures !destroy_image_view_ghost(view).alive,
{
}

/// Destroying a framebuffer preserves its id.
pub proof fn lemma_destroy_framebuffer_preserves_id(fb: FramebufferState)
    ensures destroy_framebuffer_ghost(fb).id == fb.id,
{
}

/// Destroying an image view preserves its id.
pub proof fn lemma_destroy_image_view_preserves_id(view: ImageViewState)
    ensures destroy_image_view_ghost(view).id == view.id,
{
}

// ── Attachment Dimension/Sample Validation ───────────────────────────

/// Every framebuffer attachment's image view dimensions are at least as large
/// as the framebuffer dimensions.
pub open spec fn framebuffer_attachments_dimensions_match(
    fb: FramebufferState,
    views: Map<nat, ImageViewState>,
) -> bool {
    forall|i: int| #![trigger fb.attachments[i]]
        0 <= i < fb.attachments.len() ==>
        views.contains_key(fb.attachments[i])
        && views[fb.attachments[i]].width >= fb.width
        && views[fb.attachments[i]].height >= fb.height
}

/// Every framebuffer attachment's image view sample count matches
/// the render pass attachment description's sample count.
pub open spec fn framebuffer_attachments_samples_consistent(
    fb: FramebufferState,
    views: Map<nat, ImageViewState>,
    rp: RenderPassState,
) -> bool {
    forall|i: int| #![trigger fb.attachments[i]]
        0 <= i < fb.attachments.len() ==>
        views.contains_key(fb.attachments[i])
        && i < rp.attachments.len()
        && views[fb.attachments[i]].samples == rp.attachments[i].samples
}

/// Every framebuffer attachment's image view format matches the render pass
/// attachment description's format.
pub open spec fn framebuffer_attachment_formats_match(
    fb: FramebufferState,
    views: Map<nat, ImageViewState>,
    rp: RenderPassState,
) -> bool {
    forall|i: int| #![trigger fb.attachments[i]]
        0 <= i < fb.attachments.len() ==>
        views.contains_key(fb.attachments[i])
        && i < rp.attachments.len()
        && views[fb.attachments[i]].format == rp.attachments[i].format
}

/// A framebuffer is fully validated: well-formed + dimensions match + samples consistent + formats match.
pub open spec fn framebuffer_fully_validated(
    fb: FramebufferState,
    rp: RenderPassState,
    views: Map<nat, ImageViewState>,
) -> bool {
    framebuffer_well_formed(fb, rp)
    && framebuffer_attachments_dimensions_match(fb, views)
    && framebuffer_attachments_samples_consistent(fb, views, rp)
    && framebuffer_attachment_formats_match(fb, views, rp)
}

/// A fully validated framebuffer is well-formed.
pub proof fn lemma_fully_validated_implies_well_formed(
    fb: FramebufferState,
    rp: RenderPassState,
    views: Map<nat, ImageViewState>,
)
    requires framebuffer_fully_validated(fb, rp, views),
    ensures framebuffer_well_formed(fb, rp),
{
}

/// A fully validated framebuffer has matching dimensions.
pub proof fn lemma_fully_validated_dimensions_match(
    fb: FramebufferState,
    rp: RenderPassState,
    views: Map<nat, ImageViewState>,
)
    requires framebuffer_fully_validated(fb, rp, views),
    ensures framebuffer_attachments_dimensions_match(fb, views),
{
}

/// A fully validated framebuffer has consistent sample counts.
pub proof fn lemma_fully_validated_samples_consistent(
    fb: FramebufferState,
    rp: RenderPassState,
    views: Map<nat, ImageViewState>,
)
    requires framebuffer_fully_validated(fb, rp, views),
    ensures framebuffer_attachments_samples_consistent(fb, views, rp),
{
}

/// A fully validated framebuffer has matching attachment formats.
pub proof fn lemma_fully_validated_formats_match(
    fb: FramebufferState,
    rp: RenderPassState,
    views: Map<nat, ImageViewState>,
)
    requires framebuffer_fully_validated(fb, rp, views),
    ensures framebuffer_attachment_formats_match(fb, views, rp),
{
}

/// If all views have the same format as all render pass attachments, formats match.
pub proof fn lemma_same_format_trivial(
    fb: FramebufferState,
    rp: RenderPassState,
    views: Map<nat, ImageViewState>,
    fmt: nat,
)
    requires
        framebuffer_well_formed(fb, rp),
        forall|i: int| #![trigger fb.attachments[i]]
            0 <= i < fb.attachments.len() ==>
            views.contains_key(fb.attachments[i])
            && views[fb.attachments[i]].format == fmt,
        forall|i: int| 0 <= i < rp.attachments.len() ==>
            rp.attachments[i].format == fmt,
    ensures
        framebuffer_attachment_formats_match(fb, views, rp),
{
    assert forall|i: int| #![trigger fb.attachments[i]]
        0 <= i < fb.attachments.len()
    implies
        views.contains_key(fb.attachments[i])
        && i < rp.attachments.len()
        && views[fb.attachments[i]].format == rp.attachments[i].format
    by {
        // fb.attachments.len() == rp.attachments.len() from framebuffer_well_formed
    }
}

/// If all views have samples==1 and all render pass attachments have samples==1,
/// then samples are trivially consistent.
pub proof fn lemma_single_sample_trivial(
    fb: FramebufferState,
    rp: RenderPassState,
    views: Map<nat, ImageViewState>,
)
    requires
        framebuffer_well_formed(fb, rp),
        forall|i: int| #![trigger fb.attachments[i]]
            0 <= i < fb.attachments.len() ==>
            views.contains_key(fb.attachments[i])
            && views[fb.attachments[i]].samples == 1,
        forall|i: int| 0 <= i < rp.attachments.len() ==>
            rp.attachments[i].samples == 1,
    ensures
        framebuffer_attachments_samples_consistent(fb, views, rp),
{
    assert forall|i: int| #![trigger fb.attachments[i]]
        0 <= i < fb.attachments.len()
    implies
        views.contains_key(fb.attachments[i])
        && i < rp.attachments.len()
        && views[fb.attachments[i]].samples == rp.attachments[i].samples
    by {
        // fb.attachments.len() == rp.attachments.len() from framebuffer_well_formed
    }
}

} // verus!
