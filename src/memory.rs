use vstd::prelude::*;
use crate::resource::*;
use crate::sync::*;
use crate::image_layout::*;

verus! {

///  A binding from a buffer/image to a specific offset in a memory allocation.
pub struct MemoryBinding {
    ///  The allocation this resource is bound to.
    pub allocation_id: nat,
    ///  Byte offset within the allocation.
    pub offset: nat,
}

///  Ghost state for a single VkDeviceMemory allocation.
pub struct MemoryAllocation {
    ///  Unique allocation identifier.
    pub id: nat,
    ///  Which memory heap this allocation lives on.
    pub heap_index: nat,
    ///  Size in bytes.
    pub size: nat,
    ///  False after vkFreeMemory.
    pub alive: bool,
}

///  Identifies a specific subresource of an image (mip level + array layer).
pub struct ImageSubresource {
    pub mip_level: nat,
    pub array_layer: nat,
}

///  Ghost state for a VkBuffer.
pub struct BufferState {
    ///  Unique buffer identifier.
    pub id: nat,
    ///  Size in bytes.
    pub size: nat,
    ///  Usage flags (as a set of nat constants).
    pub usage: Set<nat>,
    ///  Memory binding (None until vkBindBufferMemory).
    pub memory_binding: Option<MemoryBinding>,
    ///  Current synchronization state.
    pub sync: SyncState,
    ///  False after vkDestroyBuffer.
    pub alive: bool,
}

///  Ghost state for a VkImage.
pub struct ImageState {
    ///  Unique image identifier.
    pub id: nat,
    ///  Format (as a nat constant).
    pub format: nat,
    ///  Dimensions.
    pub width: nat,
    pub height: nat,
    pub depth: nat,
    ///  Number of mip levels.
    pub mip_levels: nat,
    ///  Number of array layers.
    pub array_layers: nat,
    ///  Usage flags.
    pub usage: Set<nat>,
    ///  Per-subresource layout tracking.
    pub layouts: Map<ImageSubresource, ImageLayout>,
    ///  Memory binding (None until vkBindImageMemory).
    pub memory_binding: Option<MemoryBinding>,
    ///  Synchronization state (coarse-grained: whole image).
    pub sync: SyncState,
    ///  False after vkDestroyImage.
    pub alive: bool,
    ///  Image tiling mode: 0 = Optimal, 1 = Linear.
    pub tiling: nat,
}

///  True iff a subresource index is valid for the given image dimensions.
pub open spec fn valid_subresource(img: ImageState, sub: ImageSubresource) -> bool {
    sub.mip_level < img.mip_levels && sub.array_layer < img.array_layers
}

///  The ResourceId corresponding to a buffer.
pub open spec fn buffer_resource_id(buf: BufferState) -> ResourceId {
    ResourceId::Buffer { id: buf.id }
}

///  The ResourceId corresponding to a specific image subresource.
pub open spec fn image_resource_id(
    img: ImageState,
    mip_level: nat,
    array_layer: nat,
) -> ResourceId {
    ResourceId::Image { id: img.id, mip_level, array_layer }
}

///  Initial per-subresource layouts: all subresources start as Undefined.
pub open spec fn initial_image_layouts(
    mip_levels: nat,
    array_layers: nat,
) -> Map<ImageSubresource, ImageLayout> {
    Map::new(
        |sub: ImageSubresource| sub.mip_level < mip_levels && sub.array_layer < array_layers,
        |sub: ImageSubresource| ImageLayout::Undefined,
    )
}

///  Ghost update: bind a buffer to a memory allocation.
pub open spec fn bind_buffer_memory(
    buf: BufferState,
    allocation_id: nat,
    offset: nat,
) -> BufferState {
    BufferState {
        memory_binding: Some(MemoryBinding { allocation_id, offset }),
        ..buf
    }
}

///  Ghost update: bind an image to a memory allocation.
pub open spec fn bind_image_memory(
    img: ImageState,
    allocation_id: nat,
    offset: nat,
) -> ImageState {
    ImageState {
        memory_binding: Some(MemoryBinding { allocation_id, offset }),
        ..img
    }
}

///  Ghost update: transition a single subresource to a new layout.
pub open spec fn transition_image_layout(
    img: ImageState,
    sub: ImageSubresource,
    new_layout: ImageLayout,
) -> ImageState {
    ImageState {
        layouts: img.layouts.insert(sub, new_layout),
        ..img
    }
}

//  ── Lemmas ──────────────────────────────────────────────────────────────

///  After binding, the buffer's memory_binding is Some.
pub proof fn lemma_bind_buffer_makes_bound(
    buf: BufferState,
    allocation_id: nat,
    offset: nat,
)
    ensures
        bind_buffer_memory(buf, allocation_id, offset).memory_binding
            == Some(MemoryBinding { allocation_id, offset }),
{
}

///  After binding, the image's memory_binding is Some.
pub proof fn lemma_bind_image_makes_bound(
    img: ImageState,
    allocation_id: nat,
    offset: nat,
)
    ensures
        bind_image_memory(img, allocation_id, offset).memory_binding
            == Some(MemoryBinding { allocation_id, offset }),
{
}

///  All valid subresources in initial_image_layouts are Undefined.
pub proof fn lemma_initial_layouts_are_undefined(
    mip_levels: nat,
    array_layers: nat,
    sub: ImageSubresource,
)
    requires
        sub.mip_level < mip_levels,
        sub.array_layer < array_layers,
    ensures
        initial_image_layouts(mip_levels, array_layers).contains_key(sub),
        initial_image_layouts(mip_levels, array_layers)[sub] == ImageLayout::Undefined,
{
}

///  Transitioning one subresource does not change other subresources' layouts.
pub proof fn lemma_layout_transition_preserves_others(
    img: ImageState,
    sub: ImageSubresource,
    other: ImageSubresource,
    new_layout: ImageLayout,
)
    requires
        sub != other,
        img.layouts.contains_key(other),
    ensures
        transition_image_layout(img, sub, new_layout).layouts.contains_key(other),
        transition_image_layout(img, sub, new_layout).layouts[other] == img.layouts[other],
{
}

///  buffer_resource_id produces a Buffer variant with the correct id.
pub proof fn lemma_buffer_resource_id_correct(buf: BufferState)
    ensures
        buffer_resource_id(buf) == (ResourceId::Buffer { id: buf.id }),
{
}

///  image_resource_id produces an Image variant with the correct fields.
pub proof fn lemma_image_resource_id_correct(
    img: ImageState,
    mip_level: nat,
    array_layer: nat,
)
    ensures
        image_resource_id(img, mip_level, array_layer)
            == (ResourceId::Image { id: img.id, mip_level, array_layer }),
{
}

} //  verus!
