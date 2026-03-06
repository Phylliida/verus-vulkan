use vstd::prelude::*;

verus! {

/// Vulkan image layout — determines how image data is arranged in memory.
///
/// Certain layouts are optimal for specific operations (e.g., transfer,
/// shader read, color attachment). Transitions between layouts are
/// constrained: you can never transition *to* Undefined or Preinitialized.
pub enum ImageLayout {
    /// Contents undefined after transition — used only as old_layout.
    Undefined,
    /// Supports all operations, but may not be optimal for any.
    General,
    /// Optimal for color attachment writes.
    ColorAttachmentOptimal,
    /// Optimal for depth/stencil read+write.
    DepthStencilAttachmentOptimal,
    /// Optimal for depth/stencil read-only (e.g., sampling in a shader).
    DepthStencilReadOnlyOptimal,
    /// Optimal for shader read-only access (sampling, input attachment).
    ShaderReadOnlyOptimal,
    /// Optimal as a transfer source.
    TransferSrcOptimal,
    /// Optimal as a transfer destination.
    TransferDstOptimal,
    /// Data arranged for host access — used only as initial layout.
    Preinitialized,
    /// For presenting to a swapchain.
    PresentSrc,
}

/// True iff a layout is "usable" — i.e., not Undefined or Preinitialized.
/// Usable layouts can be both sources and targets of transitions.
pub open spec fn is_usable_layout(layout: ImageLayout) -> bool {
    !matches!(layout, ImageLayout::Undefined | ImageLayout::Preinitialized)
}

/// A layout transition is valid iff the new layout is usable.
///
/// Vulkan forbids transitioning *to* Undefined (data becomes garbage)
/// and *to* Preinitialized (only valid as the initial layout at image
/// creation). The old layout can be anything (including Undefined for
/// "don't care about old contents").
pub open spec fn layout_transition_valid(
    old_layout: ImageLayout,
    new_layout: ImageLayout,
) -> bool {
    is_usable_layout(new_layout)
}

// ── Lemmas ──────────────────────────────────────────────────────────────

/// Transitioning from Undefined to any usable layout is valid.
pub proof fn lemma_undefined_to_any_valid(new_layout: ImageLayout)
    requires is_usable_layout(new_layout),
    ensures layout_transition_valid(ImageLayout::Undefined, new_layout),
{
}

/// Transitioning from Preinitialized to any usable layout is valid.
pub proof fn lemma_preinitialized_to_any_valid(new_layout: ImageLayout)
    requires is_usable_layout(new_layout),
    ensures layout_transition_valid(ImageLayout::Preinitialized, new_layout),
{
}

/// A transition from a usable layout to itself is valid.
pub proof fn lemma_layout_transition_reflexive(layout: ImageLayout)
    requires is_usable_layout(layout),
    ensures layout_transition_valid(layout, layout),
{
}

/// General is always a valid transition target.
pub proof fn lemma_general_compatible_with_all(old_layout: ImageLayout)
    ensures layout_transition_valid(old_layout, ImageLayout::General),
{
}

} // verus!
