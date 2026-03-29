use vstd::prelude::*;

verus! {

///  Identifies a GPU resource tracked by the synchronization model.
///
///  Each variant carries enough information to distinguish overlapping
///  sub-resources (e.g., different mip levels of the same image).
pub enum ResourceId {
    ///  A buffer, identified by a unique handle id.
    Buffer { id: nat },
    ///  A specific mip level + array layer of an image.
    Image { id: nat, mip_level: nat, array_layer: nat },
    ///  A swapchain image, identified by swapchain id + image index.
    SwapchainImage { swapchain_id: nat, image_index: nat },
    ///  A descriptor set, identified by a unique id.
    DescriptorSet { id: nat },
}

///  Two resources overlap if they refer to the same underlying memory.
///
///  Buffers overlap iff same id. Images overlap iff same id AND same
///  mip_level AND same array_layer. Swapchain images overlap iff same
///  swapchain_id AND same image_index. Different variants never overlap.
pub open spec fn resource_overlap(a: ResourceId, b: ResourceId) -> bool {
    match (a, b) {
        (ResourceId::Buffer { id: id_a }, ResourceId::Buffer { id: id_b }) => {
            id_a == id_b
        },
        (ResourceId::Image { id: id_a, mip_level: mip_a, array_layer: arr_a },
         ResourceId::Image { id: id_b, mip_level: mip_b, array_layer: arr_b }) => {
            id_a == id_b && mip_a == mip_b && arr_a == arr_b
        },
        (ResourceId::SwapchainImage { swapchain_id: sid_a, image_index: idx_a },
         ResourceId::SwapchainImage { swapchain_id: sid_b, image_index: idx_b }) => {
            sid_a == sid_b && idx_a == idx_b
        },
        (ResourceId::DescriptorSet { id: id_a },
         ResourceId::DescriptorSet { id: id_b }) => {
            id_a == id_b
        },
        _ => false,
    }
}

///  resource_overlap is reflexive.
pub proof fn lemma_resource_overlap_reflexive(r: ResourceId)
    ensures resource_overlap(r, r),
{
}

///  resource_overlap is symmetric.
pub proof fn lemma_resource_overlap_symmetric(a: ResourceId, b: ResourceId)
    requires resource_overlap(a, b),
    ensures resource_overlap(b, a),
{
}

} //  verus!
