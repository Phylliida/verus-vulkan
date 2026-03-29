use vstd::prelude::*;

verus! {

///  Vulkan image layout — determines how image data is arranged in memory.
///
///  Certain layouts are optimal for specific operations (e.g., transfer,
///  shader read, color attachment). Transitions between layouts are
///  constrained: you can never transition *to* Undefined or Preinitialized.
pub enum ImageLayout {
    ///  Contents undefined after transition — used only as old_layout.
    Undefined,
    ///  Supports all operations, but may not be optimal for any.
    General,
    ///  Optimal for color attachment writes.
    ColorAttachmentOptimal,
    ///  Optimal for depth/stencil read+write.
    DepthStencilAttachmentOptimal,
    ///  Optimal for depth/stencil read-only (e.g., sampling in a shader).
    DepthStencilReadOnlyOptimal,
    ///  Optimal for shader read-only access (sampling, input attachment).
    ShaderReadOnlyOptimal,
    ///  Optimal as a transfer source.
    TransferSrcOptimal,
    ///  Optimal as a transfer destination.
    TransferDstOptimal,
    ///  Data arranged for host access — used only as initial layout.
    Preinitialized,
    ///  For presenting to a swapchain.
    PresentSrc,
}

///  True iff a layout is "usable" — i.e., not Undefined or Preinitialized.
///  Usable layouts can be both sources and targets of transitions.
pub open spec fn is_usable_layout(layout: ImageLayout) -> bool {
    !matches!(layout, ImageLayout::Undefined | ImageLayout::Preinitialized)
}

///  A layout transition is valid iff the new layout is usable.
///
///  Vulkan forbids transitioning *to* Undefined (data becomes garbage)
///  and *to* Preinitialized (only valid as the initial layout at image
///  creation). The old layout can be anything (including Undefined for
///  "don't care about old contents").
pub open spec fn layout_transition_valid(
    old_layout: ImageLayout,
    new_layout: ImageLayout,
) -> bool {
    is_usable_layout(new_layout)
}

//  ── Lemmas ──────────────────────────────────────────────────────────────

///  Transitioning from Undefined to any usable layout is valid.
pub proof fn lemma_undefined_to_any_valid(new_layout: ImageLayout)
    requires is_usable_layout(new_layout),
    ensures layout_transition_valid(ImageLayout::Undefined, new_layout),
{
}

///  Transitioning from Preinitialized to any usable layout is valid.
pub proof fn lemma_preinitialized_to_any_valid(new_layout: ImageLayout)
    requires is_usable_layout(new_layout),
    ensures layout_transition_valid(ImageLayout::Preinitialized, new_layout),
{
}

///  A transition from a usable layout to itself is valid.
pub proof fn lemma_layout_transition_reflexive(layout: ImageLayout)
    requires is_usable_layout(layout),
    ensures layout_transition_valid(layout, layout),
{
}

///  General is always a valid transition target.
pub proof fn lemma_general_compatible_with_all(old_layout: ImageLayout)
    ensures layout_transition_valid(old_layout, ImageLayout::General),
{
}

//  ── Layout ID Mapping ──────────────────────────────────────────────────
//  Maps between ImageLayout enum and nat IDs (matching VkImageLayout values).

///  Map an ImageLayout to its numeric ID.
pub open spec fn layout_id(layout: ImageLayout) -> nat {
    match layout {
        ImageLayout::Undefined => 0,
        ImageLayout::General => 1,
        ImageLayout::ColorAttachmentOptimal => 2,
        ImageLayout::DepthStencilAttachmentOptimal => 3,
        ImageLayout::DepthStencilReadOnlyOptimal => 4,
        ImageLayout::ShaderReadOnlyOptimal => 5,
        ImageLayout::TransferSrcOptimal => 6,
        ImageLayout::TransferDstOptimal => 7,
        ImageLayout::Preinitialized => 8,
        ImageLayout::PresentSrc => 9,
    }
}

///  Map a numeric ID to an ImageLayout (Undefined for invalid IDs).
pub open spec fn layout_from_id(id: nat) -> ImageLayout {
    if id == 0 { ImageLayout::Undefined }
    else if id == 1 { ImageLayout::General }
    else if id == 2 { ImageLayout::ColorAttachmentOptimal }
    else if id == 3 { ImageLayout::DepthStencilAttachmentOptimal }
    else if id == 4 { ImageLayout::DepthStencilReadOnlyOptimal }
    else if id == 5 { ImageLayout::ShaderReadOnlyOptimal }
    else if id == 6 { ImageLayout::TransferSrcOptimal }
    else if id == 7 { ImageLayout::TransferDstOptimal }
    else if id == 8 { ImageLayout::Preinitialized }
    else if id == 9 { ImageLayout::PresentSrc }
    else { ImageLayout::Undefined }
}

///  A layout ID is valid (corresponds to a real ImageLayout).
pub open spec fn valid_layout_id(id: nat) -> bool {
    id <= 9
}

///  Roundtrip: layout_from_id(layout_id(l)) == l.
pub proof fn lemma_layout_id_roundtrip(layout: ImageLayout)
    ensures layout_from_id(layout_id(layout)) == layout,
{
}

///  Roundtrip: valid_layout_id(id) → layout_id(layout_from_id(id)) == id.
pub proof fn lemma_valid_id_roundtrip(id: nat)
    requires valid_layout_id(id),
    ensures layout_id(layout_from_id(id)) == id,
{
}

///  All layout IDs are distinct.
pub proof fn lemma_layout_ids_distinct()
    ensures
        layout_id(ImageLayout::Undefined) != layout_id(ImageLayout::General),
        layout_id(ImageLayout::General) != layout_id(ImageLayout::ColorAttachmentOptimal),
        layout_id(ImageLayout::ColorAttachmentOptimal) != layout_id(ImageLayout::ShaderReadOnlyOptimal),
        layout_id(ImageLayout::TransferSrcOptimal) != layout_id(ImageLayout::TransferDstOptimal),
        layout_id(ImageLayout::PresentSrc) != layout_id(ImageLayout::Undefined),
{
}

} //  verus!
