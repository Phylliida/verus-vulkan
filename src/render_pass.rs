use vstd::prelude::*;
use crate::flags::*;
use crate::image_layout::*;
use crate::format_properties::*;
use crate::device::*;

verus! {

// ── Load/Store Operations ─────────────────────────────────────────────

/// How the attachment contents are treated at the beginning of a render pass.
pub enum LoadOp {
    /// Preserve existing contents.
    Load,
    /// Clear to a specified value.
    Clear,
    /// Contents are undefined (driver may discard).
    DontCare,
}

/// How the attachment contents are treated at the end of a render pass.
pub enum StoreOp {
    /// Write results to memory.
    Store,
    /// Contents may be discarded.
    DontCare,
}

// ── Attachment & Subpass Types ────────────────────────────────────────

/// Describes a single framebuffer attachment in a render pass.
pub struct AttachmentDescription {
    /// Numeric format identifier (e.g., R8G8B8A8_UNORM = some nat).
    pub format: nat,
    /// Number of samples (1 for non-MSAA).
    pub samples: nat,
    /// How to handle attachment contents at load time.
    pub load_op: LoadOp,
    /// How to handle attachment contents at store time.
    pub store_op: StoreOp,
    /// Layout the attachment is in when the render pass begins.
    pub initial_layout: ImageLayout,
    /// Layout the attachment will be transitioned to when the render pass ends.
    pub final_layout: ImageLayout,
}

/// A reference from a subpass to a specific attachment.
pub struct AttachmentReference {
    /// Index into the render pass's attachment array.
    pub attachment_index: nat,
    /// Layout the attachment should be in during this subpass.
    pub layout: ImageLayout,
}

/// Describes a single subpass within a render pass.
pub struct SubpassDescription {
    /// Color attachments written by this subpass.
    pub color_attachments: Seq<AttachmentReference>,
    /// Optional depth/stencil attachment.
    pub depth_attachment: Option<AttachmentReference>,
    /// Input attachments read by this subpass (from prior subpass output).
    pub input_attachments: Seq<AttachmentReference>,
    /// Attachment indices whose contents must be preserved (not written).
    pub preserve_attachments: Set<nat>,
}

/// An execution/memory dependency between two subpasses.
pub struct SubpassDependency {
    /// Source subpass index, or None for external (before render pass).
    pub src_subpass: Option<nat>,
    /// Destination subpass index, or None for external (after render pass).
    pub dst_subpass: Option<nat>,
    /// Pipeline stages in the source that must complete.
    pub src_stages: PipelineStageFlags,
    /// Access types in the source that must be visible.
    pub src_access: AccessFlags,
    /// Pipeline stages in the destination that wait.
    pub dst_stages: PipelineStageFlags,
    /// Access types in the destination that need visibility.
    pub dst_access: AccessFlags,
}

/// The complete state of a created render pass object.
pub struct RenderPassState {
    /// Unique identifier for this render pass.
    pub id: nat,
    /// Framebuffer attachment descriptions.
    pub attachments: Seq<AttachmentDescription>,
    /// Subpass descriptions (ordered).
    pub subpasses: Seq<SubpassDescription>,
    /// Dependencies between subpasses (and external).
    pub dependencies: Seq<SubpassDependency>,
    /// Whether this render pass object is still alive (not destroyed).
    pub alive: bool,
}

// ── Layout Classification ─────────────────────────────────────────────

/// True iff the layout is valid for a color attachment.
pub open spec fn is_color_layout(layout: ImageLayout) -> bool {
    matches!(layout, ImageLayout::ColorAttachmentOptimal | ImageLayout::General)
}

/// True iff the layout is valid for a depth/stencil attachment.
pub open spec fn is_depth_layout(layout: ImageLayout) -> bool {
    matches!(layout,
        ImageLayout::DepthStencilAttachmentOptimal
        | ImageLayout::DepthStencilReadOnlyOptimal
        | ImageLayout::General
    )
}

// ── Well-Formedness Specs ─────────────────────────────────────────────

/// An attachment reference is valid: index in bounds and layout is usable.
pub open spec fn attachment_ref_valid(
    rp: RenderPassState,
    aref: AttachmentReference,
) -> bool {
    aref.attachment_index < rp.attachments.len()
    && is_usable_layout(aref.layout)
}

/// A subpass is well-formed within a render pass.
///
/// - All color attachment refs are valid and use color-compatible layouts.
/// - The depth attachment (if present) is valid and uses a depth-compatible layout.
/// - All input attachment refs are valid.
/// - All preserve attachment indices are in bounds.
/// - Preserved attachments are not also used as color, depth, or input.
pub open spec fn subpass_well_formed(
    rp: RenderPassState,
    subpass_idx: nat,
) -> bool
    recommends subpass_idx < rp.subpasses.len(),
{
    let sp = rp.subpasses[subpass_idx as int];

    // Color attachments valid with color-compatible layouts
    (forall|i: int| 0 <= i < sp.color_attachments.len() ==> {
        &&& attachment_ref_valid(rp, sp.color_attachments[i])
        &&& is_color_layout(sp.color_attachments[i].layout)
        &&& !is_depth_layout(sp.color_attachments[i].layout)
            || sp.color_attachments[i].layout == ImageLayout::General
    })

    // Depth attachment valid with depth-compatible layout
    && match sp.depth_attachment {
        Some(dref) => {
            &&& attachment_ref_valid(rp, dref)
            &&& is_depth_layout(dref.layout)
            &&& !matches!(dref.layout, ImageLayout::ColorAttachmentOptimal)
        },
        None => true,
    }

    // Input attachments valid
    && (forall|i: int| 0 <= i < sp.input_attachments.len() ==>
        attachment_ref_valid(rp, sp.input_attachments[i]))

    // Preserve attachments in bounds
    && (forall|idx: nat| sp.preserve_attachments.contains(idx) ==>
        idx < rp.attachments.len())

    // Preserved attachments not used as color, depth, or input
    && (forall|idx: nat| sp.preserve_attachments.contains(idx) ==> {
        &&& (forall|i: int| 0 <= i < sp.color_attachments.len() ==>
            sp.color_attachments[i].attachment_index != idx)
        &&& match sp.depth_attachment {
            Some(dref) => dref.attachment_index != idx,
            None => true,
        }
        &&& (forall|i: int| 0 <= i < sp.input_attachments.len() ==>
            sp.input_attachments[i].attachment_index != idx)
    })
}

/// A subpass dependency is well-formed.
///
/// - Subpass indices (if Some) are in bounds.
/// - For internal dependencies (both Some), dst > src (acyclicity).
pub open spec fn dependency_well_formed(
    rp: RenderPassState,
    dep: SubpassDependency,
) -> bool {
    // Source subpass in bounds if specified
    (match dep.src_subpass {
        Some(s) => s < rp.subpasses.len(),
        None => true,
    })
    // Destination subpass in bounds if specified
    && (match dep.dst_subpass {
        Some(d) => d < rp.subpasses.len(),
        None => true,
    })
    // Internal dependencies must have dst > src (acyclicity)
    && (match (dep.src_subpass, dep.dst_subpass) {
        (Some(s), Some(d)) => d > s,
        _ => true,
    })
}

/// A render pass is well-formed.
///
/// - At least one subpass.
/// - All attachments have usable final layouts.
/// - All subpasses are well-formed.
/// - All dependencies are well-formed.
pub open spec fn render_pass_well_formed(rp: RenderPassState) -> bool {
    // At least one subpass
    rp.subpasses.len() > 0

    // All attachments have usable final layouts
    && (forall|i: int| 0 <= i < rp.attachments.len() ==>
        is_usable_layout(rp.attachments[i].final_layout))

    // All subpasses well-formed
    && (forall|s: int| 0 <= s < rp.subpasses.len() ==>
        #[trigger] subpass_well_formed(rp, s as nat))

    // All dependencies well-formed
    && (forall|d: int| 0 <= d < rp.dependencies.len() ==>
        dependency_well_formed(rp, rp.dependencies[d]))
}

// ── Accessors ─────────────────────────────────────────────────────────

/// Initial layout of attachment i.
pub open spec fn attachment_initial_layout(
    rp: RenderPassState, i: nat,
) -> ImageLayout
    recommends i < rp.attachments.len(),
{
    rp.attachments[i as int].initial_layout
}

/// Final layout of attachment i.
pub open spec fn attachment_final_layout(
    rp: RenderPassState, i: nat,
) -> ImageLayout
    recommends i < rp.attachments.len(),
{
    rp.attachments[i as int].final_layout
}

/// Number of color attachments in subpass s.
pub open spec fn subpass_color_attachment_count(
    rp: RenderPassState, s: nat,
) -> nat
    recommends s < rp.subpasses.len(),
{
    rp.subpasses[s as int].color_attachments.len()
}

/// Whether subpass s has a depth attachment.
pub open spec fn subpass_has_depth(
    rp: RenderPassState, s: nat,
) -> bool
    recommends s < rp.subpasses.len(),
{
    rp.subpasses[s as int].depth_attachment.is_some()
}

/// Whether subpass s references attachment att_idx (as color, depth, or input).
pub open spec fn subpass_uses_attachment(
    rp: RenderPassState, s: nat, att_idx: nat,
) -> bool
    recommends s < rp.subpasses.len(),
{
    let sp = rp.subpasses[s as int];

    // Used as color attachment
    (exists|i: int| 0 <= i < sp.color_attachments.len()
        && sp.color_attachments[i].attachment_index == att_idx)

    // Used as depth attachment
    || match sp.depth_attachment {
        Some(dref) => dref.attachment_index == att_idx,
        None => false,
    }

    // Used as input attachment
    || (exists|i: int| 0 <= i < sp.input_attachments.len()
        && sp.input_attachments[i].attachment_index == att_idx)
}

// ── Lemmas ────────────────────────────────────────────────────────────

/// A well-formed render pass has at least one subpass.
pub proof fn lemma_well_formed_has_subpasses(rp: RenderPassState)
    requires render_pass_well_formed(rp),
    ensures rp.subpasses.len() > 0,
{
}

/// A well-formed render pass has usable final layouts for all attachments.
pub proof fn lemma_well_formed_attachments_usable_final(
    rp: RenderPassState, i: nat,
)
    requires
        render_pass_well_formed(rp),
        i < rp.attachments.len(),
    ensures
        is_usable_layout(attachment_final_layout(rp, i)),
{
}

/// In a well-formed render pass, all attachment refs in a subpass have valid indices.
pub proof fn lemma_well_formed_subpass_refs_in_bounds(
    rp: RenderPassState, s: nat,
)
    requires
        render_pass_well_formed(rp),
        s < rp.subpasses.len(),
    ensures
        // Color refs in bounds
        forall|i: int| 0 <= i < rp.subpasses[s as int].color_attachments.len()
            ==> rp.subpasses[s as int].color_attachments[i].attachment_index
                < rp.attachments.len(),
        // Depth ref in bounds
        rp.subpasses[s as int].depth_attachment.is_some()
            ==> rp.subpasses[s as int].depth_attachment.unwrap().attachment_index
                < rp.attachments.len(),
        // Input refs in bounds
        forall|i: int| 0 <= i < rp.subpasses[s as int].input_attachments.len()
            ==> rp.subpasses[s as int].input_attachments[i].attachment_index
                < rp.attachments.len(),
{
    // Trigger the quantifier in render_pass_well_formed via int path
    let s_int: int = s as int;
    assert(subpass_well_formed(rp, s_int as nat));
}

/// Internal dependencies have dst > src (acyclicity).
pub proof fn lemma_dependencies_acyclic(rp: RenderPassState, i: nat)
    requires
        render_pass_well_formed(rp),
        i < rp.dependencies.len(),
        rp.dependencies[i as int].src_subpass.is_some(),
        rp.dependencies[i as int].dst_subpass.is_some(),
    ensures
        rp.dependencies[i as int].dst_subpass.unwrap()
            > rp.dependencies[i as int].src_subpass.unwrap(),
{
    assert(dependency_well_formed(rp, rp.dependencies[i as int]));
}

/// Color attachment layouts are not DepthStencil-exclusive layouts.
pub proof fn lemma_color_not_depth_layout(
    rp: RenderPassState, s: nat, i: int,
)
    requires
        render_pass_well_formed(rp),
        s < rp.subpasses.len(),
        0 <= i < rp.subpasses[s as int].color_attachments.len(),
    ensures
        is_color_layout(rp.subpasses[s as int].color_attachments[i].layout),
{
    let s_int: int = s as int;
    assert(subpass_well_formed(rp, s_int as nat));
}

/// Depth attachment layout is not ColorAttachmentOptimal.
pub proof fn lemma_depth_not_color_layout(
    rp: RenderPassState, s: nat,
)
    requires
        render_pass_well_formed(rp),
        s < rp.subpasses.len(),
        rp.subpasses[s as int].depth_attachment.is_some(),
    ensures ({
        let layout = rp.subpasses[s as int].depth_attachment.unwrap().layout;
        !(layout == ImageLayout::ColorAttachmentOptimal)
    }),
{
    let s_int: int = s as int;
    assert(subpass_well_formed(rp, s_int as nat));
}

/// Transition from initial to final layout for each attachment is valid
/// (final layout is usable, so the transition is valid).
pub proof fn lemma_initial_to_final_valid(
    rp: RenderPassState, i: nat,
)
    requires
        render_pass_well_formed(rp),
        i < rp.attachments.len(),
    ensures
        layout_transition_valid(
            attachment_initial_layout(rp, i),
            attachment_final_layout(rp, i),
        ),
{
}

/// A preserved attachment is not used as color, depth, or input in that subpass.
pub proof fn lemma_preserve_not_used(
    rp: RenderPassState, s: nat, att: nat,
)
    requires
        render_pass_well_formed(rp),
        s < rp.subpasses.len(),
        rp.subpasses[s as int].preserve_attachments.contains(att),
    ensures
        !subpass_uses_attachment(rp, s, att),
{
    let s_int: int = s as int;
    assert(subpass_well_formed(rp, s_int as nat));
    let sp = rp.subpasses[s as int];

    // Color: none of the color attachments reference att
    assert forall|i: int| 0 <= i < sp.color_attachments.len()
    implies sp.color_attachments[i].attachment_index != att
    by {
        // From subpass_well_formed's preserve constraint
    }

    // Depth: if present, doesn't reference att
    // (from subpass_well_formed's preserve constraint)

    // Input: none of the input attachments reference att
    assert forall|i: int| 0 <= i < sp.input_attachments.len()
    implies sp.input_attachments[i].attachment_index != att
    by {
        // From subpass_well_formed's preserve constraint
    }
}

// ── Format Validation ────────────────────────────────────────────────────

/// Whether attachment `att_idx` is used as a color attachment in any subpass.
pub open spec fn attachment_used_as_color(rp: RenderPassState, att_idx: nat) -> bool {
    exists|s: int, i: int|
        0 <= s < rp.subpasses.len()
        && 0 <= i < rp.subpasses[s].color_attachments.len()
        && rp.subpasses[s].color_attachments[i].attachment_index == att_idx
}

/// Whether attachment `att_idx` is used as a depth attachment in any subpass.
pub open spec fn attachment_used_as_depth(rp: RenderPassState, att_idx: nat) -> bool {
    exists|s: int|
        0 <= s < rp.subpasses.len()
        && rp.subpasses[s].depth_attachment.is_some()
        && rp.subpasses[s].depth_attachment.unwrap().attachment_index == att_idx
}

/// All attachments in the render pass have adequate format features for their roles.
pub open spec fn render_pass_formats_supported(
    rp: RenderPassState,
    dev: DeviceState,
) -> bool {
    forall|att_idx: nat| #![trigger dev.format_properties.contains_key(rp.attachments[att_idx as int].format)]
        att_idx < rp.attachments.len() ==> {
            let fmt = rp.attachments[att_idx as int].format;
            dev.format_properties.contains_key(fmt)
            && (attachment_used_as_color(rp, att_idx)
                ==> format_supports_color_attachment(dev.format_properties[fmt]))
            && (attachment_used_as_depth(rp, att_idx)
                ==> format_supports_depth_stencil(dev.format_properties[fmt]))
        }
}

/// If formats are supported and attachment is used as color, its format supports color.
pub proof fn lemma_formats_supported_color(
    rp: RenderPassState, dev: DeviceState, att_idx: nat,
)
    requires
        render_pass_formats_supported(rp, dev),
        att_idx < rp.attachments.len(),
        attachment_used_as_color(rp, att_idx),
    ensures
        dev.format_properties.contains_key(rp.attachments[att_idx as int].format),
        format_supports_color_attachment(
            dev.format_properties[rp.attachments[att_idx as int].format]),
{
    let fmt = rp.attachments[att_idx as int].format;
    assert(dev.format_properties.contains_key(fmt));
}

/// If formats are supported and attachment is used as depth, its format supports depth.
pub proof fn lemma_formats_supported_depth(
    rp: RenderPassState, dev: DeviceState, att_idx: nat,
)
    requires
        render_pass_formats_supported(rp, dev),
        att_idx < rp.attachments.len(),
        attachment_used_as_depth(rp, att_idx),
    ensures
        dev.format_properties.contains_key(rp.attachments[att_idx as int].format),
        format_supports_depth_stencil(
            dev.format_properties[rp.attachments[att_idx as int].format]),
{
    let fmt = rp.attachments[att_idx as int].format;
    assert(dev.format_properties.contains_key(fmt));
}

// ── Ghost Destroy ────────────────────────────────────────────────────

/// Ghost update: destroy a render pass.
pub open spec fn destroy_render_pass_ghost(rp: RenderPassState) -> RenderPassState {
    RenderPassState {
        alive: false,
        ..rp
    }
}

/// After destroying, a render pass is not alive.
pub proof fn lemma_destroy_render_pass_not_alive(rp: RenderPassState)
    ensures !destroy_render_pass_ghost(rp).alive,
{
}

/// Destroying a render pass preserves its id.
pub proof fn lemma_destroy_render_pass_preserves_id(rp: RenderPassState)
    ensures destroy_render_pass_ghost(rp).id == rp.id,
{
}

} // verus!
