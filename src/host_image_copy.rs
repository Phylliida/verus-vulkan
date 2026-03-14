use vstd::prelude::*;
use crate::resource::*;
use crate::memory::*;
use crate::image_layout::*;
use crate::image_layout_fsm::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// Format feature bit for host image transfer.
pub open spec fn FEATURE_HOST_IMAGE_TRANSFER() -> nat { 0x4000_0000 }

/// A region for host image copy (VK_EXT_host_image_copy).
pub struct HostImageCopyRegion {
    pub image_subresource: ImageSubresource,
    pub image_offset_x: nat,
    pub image_offset_y: nat,
    pub image_offset_z: nat,
    pub image_extent_width: nat,
    pub image_extent_height: nat,
    pub image_extent_depth: nat,
    pub memory_row_length: nat,
    pub memory_image_height: nat,
}

/// Info for a host-to-image copy.
pub struct HostCopyToImageInfo {
    pub image: ResourceId,
    pub image_layout: ImageLayout,
    pub regions: Seq<HostImageCopyRegion>,
}

/// Info for an image-to-host copy.
pub struct HostCopyFromImageInfo {
    pub image: ResourceId,
    pub image_layout: ImageLayout,
    pub regions: Seq<HostImageCopyRegion>,
}

/// Device limits for host image copy.
pub struct HostImageCopyLimits {
    pub host_image_copy_memory_alignment: nat,
    pub identical_memory_layout_supported: bool,
}

/// A host-side image layout transition.
pub struct HostImageTransition {
    pub image: ResourceId,
    pub old_layout: ImageLayout,
    pub new_layout: ImageLayout,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// A copy region is within the image bounds.
pub open spec fn host_copy_region_in_bounds(
    region: HostImageCopyRegion,
    image: ImageState,
) -> bool {
    region.image_offset_x + region.image_extent_width <= image.width
    && region.image_offset_y + region.image_extent_height <= image.height
    && region.image_offset_z + region.image_extent_depth <= image.depth
}

/// Layout is valid for a source (read) operation.
pub open spec fn host_copy_layout_valid_for_src(layout: ImageLayout) -> bool {
    matches!(layout, ImageLayout::General | ImageLayout::TransferSrcOptimal)
}

/// Layout is valid for a destination (write) operation.
pub open spec fn host_copy_layout_valid_for_dst(layout: ImageLayout) -> bool {
    matches!(layout, ImageLayout::General | ImageLayout::TransferDstOptimal)
}

/// Host copy to image is valid.
pub open spec fn host_copy_to_image_valid(
    info: HostCopyToImageInfo,
    image: ImageState,
    format_supports: bool,
) -> bool {
    image.alive
    && host_copy_layout_valid_for_dst(info.image_layout)
    && format_supports
    && info.regions.len() > 0
    && (forall|i: int| 0 <= i < info.regions.len() ==>
        host_copy_region_in_bounds(info.regions[i], image))
}

/// Host copy from image is valid.
pub open spec fn host_copy_from_image_valid(
    info: HostCopyFromImageInfo,
    image: ImageState,
    format_supports: bool,
) -> bool {
    image.alive
    && host_copy_layout_valid_for_src(info.image_layout)
    && format_supports
    && info.regions.len() > 0
    && (forall|i: int| 0 <= i < info.regions.len() ==>
        host_copy_region_in_bounds(info.regions[i], image))
}

/// Host image-to-image copy is valid.
pub open spec fn host_image_to_image_valid(
    src_layout: ImageLayout,
    dst_layout: ImageLayout,
    src_image: ImageState,
    dst_image: ImageState,
    src_format_supports: bool,
    dst_format_supports: bool,
) -> bool {
    src_image.alive
    && dst_image.alive
    && host_copy_layout_valid_for_src(src_layout)
    && host_copy_layout_valid_for_dst(dst_layout)
    && src_format_supports
    && dst_format_supports
}

/// A host image layout transition is valid.
pub open spec fn host_transition_valid(transition: HostImageTransition) -> bool {
    layout_transition_valid(transition.old_layout, transition.new_layout)
}

/// Ghost: apply a host transition to the layout map.
pub open spec fn host_transition_ghost(
    map: ImageLayoutMap,
    transition: HostImageTransition,
) -> ImageLayoutMap {
    map.insert(transition.image, transition.new_layout)
}

/// Effective row length: if 0, use extent width.
pub open spec fn effective_row_length(region: HostImageCopyRegion) -> nat {
    if region.memory_row_length == 0 {
        region.image_extent_width
    } else {
        region.memory_row_length
    }
}

/// Effective image height: if 0, use extent height.
pub open spec fn effective_image_height(region: HostImageCopyRegion) -> nat {
    if region.memory_image_height == 0 {
        region.image_extent_height
    } else {
        region.memory_image_height
    }
}

/// Memory requirement for a host copy region.
pub open spec fn host_copy_memory_requirement(
    region: HostImageCopyRegion,
    texel_size: nat,
) -> nat {
    effective_row_length(region) * effective_image_height(region)
        * region.image_extent_depth * texel_size
}

/// Host copy alignment is valid.
pub open spec fn host_copy_alignment_valid(address: nat, limits: HostImageCopyLimits) -> bool {
    limits.host_image_copy_memory_alignment > 0
    && address % limits.host_image_copy_memory_alignment == 0
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// In-bounds region has positive extent when image has positive dimensions.
pub proof fn lemma_region_in_bounds_positive_extent(
    region: HostImageCopyRegion,
    image: ImageState,
)
    requires
        host_copy_region_in_bounds(region, image),
        image.width > 0,
        image.height > 0,
        image.depth > 0,
        region.image_offset_x < image.width,
        region.image_offset_y < image.height,
        region.image_offset_z < image.depth,
    ensures
        region.image_extent_width > 0 || region.image_offset_x + region.image_extent_width <= image.width,
{
}

/// General layout is always valid for source.
pub proof fn lemma_src_layout_allows_general()
    ensures host_copy_layout_valid_for_src(ImageLayout::General),
{
}

/// General layout is always valid for destination.
pub proof fn lemma_dst_layout_allows_general()
    ensures host_copy_layout_valid_for_dst(ImageLayout::General),
{
}

/// After transition, the map contains the new layout.
pub proof fn lemma_transition_updates_layout(
    map: ImageLayoutMap,
    transition: HostImageTransition,
)
    ensures
        host_transition_ghost(map, transition).contains_key(transition.image),
        host_transition_ghost(map, transition)[transition.image] == transition.new_layout,
{
}

/// Transition doesn't affect other images.
pub proof fn lemma_transition_preserves_other_images(
    map: ImageLayoutMap,
    transition: HostImageTransition,
    other: ResourceId,
)
    requires other !== transition.image,
    ensures
        host_transition_ghost(map, transition).contains_key(other)
            == map.contains_key(other),
        map.contains_key(other) ==>
            host_transition_ghost(map, transition)[other] == map[other],
{
}

/// Valid copy requires format support.
pub proof fn lemma_copy_requires_host_transfer_feature(
    info: HostCopyToImageInfo,
    image: ImageState,
    format_supports: bool,
)
    requires host_copy_to_image_valid(info, image, format_supports),
    ensures format_supports,
{
}

/// Zero memory_row_length uses extent width.
pub proof fn lemma_zero_row_length_uses_extent(region: HostImageCopyRegion)
    requires region.memory_row_length == 0,
    ensures effective_row_length(region) == region.image_extent_width,
{
}

/// Host transition respects layout validity rules.
pub proof fn lemma_host_transition_respects_layout_rules(
    transition: HostImageTransition,
)
    requires host_transition_valid(transition),
    ensures layout_transition_valid(transition.old_layout, transition.new_layout),
{
}

/// Non-zero region with non-zero texel size has positive memory requirement.
pub proof fn lemma_memory_requirement_positive(
    region: HostImageCopyRegion,
    texel_size: nat,
)
    requires
        region.image_extent_width > 0,
        region.image_extent_height > 0,
        region.image_extent_depth > 0,
        texel_size > 0,
    ensures host_copy_memory_requirement(region, texel_size) > 0,
{
    let rl = effective_row_length(region);
    let ih = effective_image_height(region);
    assert(rl > 0) by {
        if region.memory_row_length == 0 {
            assert(rl == region.image_extent_width);
        } else {
            assert(rl == region.memory_row_length);
        }
    }
    assert(ih > 0) by {
        if region.memory_image_height == 0 {
            assert(ih == region.image_extent_height);
        } else {
            assert(ih == region.memory_image_height);
        }
    }
    vstd::arithmetic::mul::lemma_mul_strictly_positive(rl as int, ih as int);
    vstd::arithmetic::mul::lemma_mul_strictly_positive(
        (rl * ih) as int,
        region.image_extent_depth as int,
    );
    vstd::arithmetic::mul::lemma_mul_strictly_positive(
        (rl * ih * region.image_extent_depth) as int,
        texel_size as int,
    );
}

/// TransferSrcOptimal is valid for source.
pub proof fn lemma_transfer_src_valid_for_src()
    ensures host_copy_layout_valid_for_src(ImageLayout::TransferSrcOptimal),
{
}

/// TransferDstOptimal is valid for destination.
pub proof fn lemma_transfer_dst_valid_for_dst()
    ensures host_copy_layout_valid_for_dst(ImageLayout::TransferDstOptimal),
{
}

} // verus!
