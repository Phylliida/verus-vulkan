use vstd::prelude::*;
use crate::resource::*;
use crate::image_layout::*;
use crate::memory::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// A region for an image-to-image copy.
pub struct ImageCopyRegion {
    pub src_subresource: ImageSubresource,
    pub src_offset_x: nat,
    pub src_offset_y: nat,
    pub src_offset_z: nat,
    pub dst_subresource: ImageSubresource,
    pub dst_offset_x: nat,
    pub dst_offset_y: nat,
    pub dst_offset_z: nat,
    pub extent_width: nat,
    pub extent_height: nat,
    pub extent_depth: nat,
}

/// A region for a buffer-to-image or image-to-buffer copy.
pub struct BufferImageCopyRegion {
    pub buffer_offset: nat,
    pub buffer_row_length: nat,
    pub buffer_image_height: nat,
    pub image_subresource: ImageSubresource,
    pub image_offset_x: nat,
    pub image_offset_y: nat,
    pub image_offset_z: nat,
    pub image_extent_width: nat,
    pub image_extent_height: nat,
    pub image_extent_depth: nat,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// Whether an image layout is valid as a copy source.
pub open spec fn valid_copy_src_layout(layout: ImageLayout) -> bool {
    layout == ImageLayout::TransferSrcOptimal
    || layout == ImageLayout::General
}

/// Whether an image layout is valid as a copy destination.
pub open spec fn valid_copy_dst_layout(layout: ImageLayout) -> bool {
    layout == ImageLayout::TransferDstOptimal
    || layout == ImageLayout::General
}

/// A copy region is within the bounds of the source image.
pub open spec fn region_in_src_bounds(
    region: ImageCopyRegion,
    src: ImageState,
) -> bool {
    region.src_offset_x + region.extent_width <= src.width
    && region.src_offset_y + region.extent_height <= src.height
    && region.src_offset_z + region.extent_depth <= src.depth
}

/// A copy region is within the bounds of the destination image.
pub open spec fn region_in_dst_bounds(
    region: ImageCopyRegion,
    dst: ImageState,
) -> bool {
    region.dst_offset_x + region.extent_width <= dst.width
    && region.dst_offset_y + region.extent_height <= dst.height
    && region.dst_offset_z + region.extent_depth <= dst.depth
}

/// An image copy is valid: layouts, bounds, formats compatible, both alive.
pub open spec fn copy_image_valid(
    src: ImageState,
    dst: ImageState,
    src_layout: ImageLayout,
    dst_layout: ImageLayout,
    regions: Seq<ImageCopyRegion>,
) -> bool {
    src.alive && dst.alive
    && valid_copy_src_layout(src_layout)
    && valid_copy_dst_layout(dst_layout)
    && src.format == dst.format
    && (forall|i: int| 0 <= i < regions.len() ==>
        region_in_src_bounds(#[trigger] regions[i], src)
        && region_in_dst_bounds(regions[i], dst))
}

/// Buffer-image copy region is within image bounds.
pub open spec fn buffer_image_region_in_bounds(
    region: BufferImageCopyRegion,
    image: ImageState,
) -> bool {
    region.image_offset_x + region.image_extent_width <= image.width
    && region.image_offset_y + region.image_extent_height <= image.height
    && region.image_offset_z + region.image_extent_depth <= image.depth
}

/// Buffer-image copy region fits in buffer.
pub open spec fn buffer_image_region_fits_buffer(
    region: BufferImageCopyRegion,
    buffer: BufferState,
) -> bool {
    // Simplified: the buffer must have enough space from the offset
    // for the full image data. Actual Vulkan uses row_length and image_height
    // for tight packing, but this is a conservative bound.
    region.buffer_offset
        + region.image_extent_width * region.image_extent_height * region.image_extent_depth
        <= buffer.size
}

/// A copy from buffer to image is valid.
pub open spec fn copy_buffer_to_image_valid(
    buffer: BufferState,
    image: ImageState,
    dst_layout: ImageLayout,
    regions: Seq<BufferImageCopyRegion>,
) -> bool {
    buffer.alive && image.alive
    && valid_copy_dst_layout(dst_layout)
    && (forall|i: int| 0 <= i < regions.len() ==>
        buffer_image_region_in_bounds(#[trigger] regions[i], image)
        && buffer_image_region_fits_buffer(regions[i], buffer))
}

/// A copy from image to buffer is valid.
pub open spec fn copy_image_to_buffer_valid(
    image: ImageState,
    buffer: BufferState,
    src_layout: ImageLayout,
    regions: Seq<BufferImageCopyRegion>,
) -> bool {
    image.alive && buffer.alive
    && valid_copy_src_layout(src_layout)
    && (forall|i: int| 0 <= i < regions.len() ==>
        buffer_image_region_in_bounds(#[trigger] regions[i], image)
        && buffer_image_region_fits_buffer(regions[i], buffer))
}

/// A blit operation is valid: layouts correct, both alive.
/// (Blit also requires format support for linear filtering, but we
/// abstract that as a precondition.)
pub open spec fn blit_image_valid(
    src: ImageState,
    dst: ImageState,
    src_layout: ImageLayout,
    dst_layout: ImageLayout,
) -> bool {
    src.alive && dst.alive
    && valid_copy_src_layout(src_layout)
    && valid_copy_dst_layout(dst_layout)
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// TransferSrcOptimal is a valid source layout.
pub proof fn lemma_transfer_src_optimal_valid()
    ensures valid_copy_src_layout(ImageLayout::TransferSrcOptimal),
{
}

/// TransferDstOptimal is a valid destination layout.
pub proof fn lemma_transfer_dst_optimal_valid()
    ensures valid_copy_dst_layout(ImageLayout::TransferDstOptimal),
{
}

/// General layout is valid for both source and destination.
pub proof fn lemma_general_layout_valid_both()
    ensures
        valid_copy_src_layout(ImageLayout::General),
        valid_copy_dst_layout(ImageLayout::General),
{
}

/// An empty regions list trivially makes image copy valid
/// (given layout and format constraints).
pub proof fn lemma_empty_regions_copy_valid(
    src: ImageState,
    dst: ImageState,
    src_layout: ImageLayout,
    dst_layout: ImageLayout,
)
    requires
        src.alive && dst.alive,
        valid_copy_src_layout(src_layout),
        valid_copy_dst_layout(dst_layout),
        src.format == dst.format,
    ensures
        copy_image_valid(src, dst, src_layout, dst_layout, Seq::empty()),
{
}

/// copy_image_valid implies both images are alive.
pub proof fn lemma_copy_valid_implies_alive(
    src: ImageState,
    dst: ImageState,
    src_layout: ImageLayout,
    dst_layout: ImageLayout,
    regions: Seq<ImageCopyRegion>,
)
    requires copy_image_valid(src, dst, src_layout, dst_layout, regions),
    ensures src.alive && dst.alive,
{
}

/// copy_image_valid implies formats match.
pub proof fn lemma_copy_valid_implies_format_match(
    src: ImageState,
    dst: ImageState,
    src_layout: ImageLayout,
    dst_layout: ImageLayout,
    regions: Seq<ImageCopyRegion>,
)
    requires copy_image_valid(src, dst, src_layout, dst_layout, regions),
    ensures src.format == dst.format,
{
}

/// ColorAttachmentOptimal is NOT a valid copy source layout.
pub proof fn lemma_color_attachment_not_copy_src()
    ensures !valid_copy_src_layout(ImageLayout::ColorAttachmentOptimal),
{
}

/// Undefined is NOT a valid copy source or destination layout.
pub proof fn lemma_undefined_not_copy_layout()
    ensures
        !valid_copy_src_layout(ImageLayout::Undefined),
        !valid_copy_dst_layout(ImageLayout::Undefined),
{
}

} // verus!
