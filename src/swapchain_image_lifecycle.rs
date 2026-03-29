use vstd::prelude::*;
use crate::memory::*;
use crate::sync::*;
use crate::flags::*;
use crate::resource::*;
use crate::swapchain::SwapchainImageInfo;

verus! {

//  ── Image-id counter management ──────────────────────────────────────

///  Invariant: all image IDs currently in the caller's ghost map are
///  below the global counter. This ensures fresh IDs from the counter
///  never collide with existing entries.
pub open spec fn all_image_ids_below(images: Map<nat, ImageState>, counter: nat) -> bool {
    forall|id: nat| images.contains_key(id) ==> id < counter
}

///  If all IDs are below the counter, then IDs starting at the counter
///  are guaranteed to be absent from the map.
pub proof fn lemma_counter_ensures_fresh_ids(
    images: Map<nat, ImageState>,
    counter: nat,
    count: nat,
)
    requires all_image_ids_below(images, counter),
    ensures forall|i: nat| #![trigger images.contains_key(counter + i)]
        i < count ==> !images.contains_key(counter + i),
{
    assert forall|i: nat| #[trigger] images.contains_key(counter + i)
        && i < count implies !images.contains_key(counter + i) by {
        //  counter + i >= counter > any existing key
    }
}

///  After rotating (killing old_id, inserting new_id), the counter
///  invariant is maintained — both old_id's killed entry and new_id's
///  alive entry have IDs below the counter.
pub proof fn lemma_rotate_maintains_counter(
    images: Map<nat, ImageState>,
    old_image_id: nat,
    new_image_id: nat,
    image_template: ImageState,
    counter: nat,
)
    requires
        all_image_ids_below(images, counter),
        new_image_id < counter,
    ensures
        all_image_ids_below(
            acquire_rotate_images(images, old_image_id, new_image_id, image_template),
            counter,
        ),
{
    let rotated = acquire_rotate_images(images, old_image_id, new_image_id, image_template);
    assert forall|id: nat| rotated.contains_key(id) implies id < counter by {
        //  new_image_id < counter by requires
        //  old_image_id was already in images (or not inserted), so < counter
        //  all other keys are from images, so < counter
    }
}

//  ── Image template construction ──────────────────────────────────────

///  Construct a full `ImageState` for a swapchain image from the
///  swapchain's image info. Fills in sensible defaults:
///  - depth=1, mip_levels=1, array_layers=1 (swapchain images are 2D)
///  - tiling=0 (VK_IMAGE_TILING_OPTIMAL)
///  - layouts=empty, memory_binding=None (implicit swapchain memory)
///  - sync: fresh (no prior reads/writes), resource = SwapchainImage
///  - alive=true
pub open spec fn make_swapchain_image_state(
    info: SwapchainImageInfo,
    image_id: nat,
    swapchain_id: nat,
    image_index: nat,
) -> ImageState {
    ImageState {
        id: image_id,
        format: info.format,
        width: info.width,
        height: info.height,
        depth: 1,
        mip_levels: 1,
        array_layers: 1,
        usage: info.usage,
        layouts: Map::empty(),
        memory_binding: None,
        sync: SyncState {
            resource: ResourceId::SwapchainImage { swapchain_id, image_index },
            last_write: None,
            last_reads: Seq::empty(),
            write_stages: PipelineStageFlags { stages: Set::empty() },
            write_accesses: AccessFlags { accesses: Set::empty() },
            read_stages: PipelineStageFlags { stages: Set::empty() },
            read_accesses: AccessFlags { accesses: Set::empty() },
        },
        alive: true,
        tiling: 0,
    }
}

///  The template always produces an alive image.
pub proof fn lemma_make_swapchain_image_state_alive(
    info: SwapchainImageInfo,
    image_id: nat,
    swapchain_id: nat,
    image_index: nat,
)
    ensures make_swapchain_image_state(info, image_id, swapchain_id, image_index).alive,
{
}

//  ── Image rotation (acquire) ─────────────────────────────────────────

///  Ghost update: after acquiring a swapchain image, mark the old image id as
///  dead and insert the new image id as alive in the caller's images map.
///
///  This ensures that descriptors bound to the old image id will fail
///  `descriptor_binding_resource_alive` (since `images[old_id].alive == false`),
///  forcing the caller to re-bind descriptors to the new image id.
pub open spec fn acquire_rotate_images(
    images: Map<nat, ImageState>,
    old_image_id: nat,
    new_image_id: nat,
    image_template: ImageState,
) -> Map<nat, ImageState> {
    let killed = if images.contains_key(old_image_id) {
        images.insert(old_image_id, ImageState { alive: false, ..images[old_image_id] })
    } else {
        images
    };
    killed.insert(new_image_id, ImageState { alive: true, ..image_template })
}

///  After rotation, the old image id is dead.
pub proof fn lemma_old_image_dead_after_rotate(
    images: Map<nat, ImageState>,
    old_image_id: nat,
    new_image_id: nat,
    image_template: ImageState,
)
    requires
        images.contains_key(old_image_id),
        old_image_id != new_image_id,
    ensures
        acquire_rotate_images(images, old_image_id, new_image_id, image_template)
            .contains_key(old_image_id),
        !acquire_rotate_images(images, old_image_id, new_image_id, image_template)
            [old_image_id].alive,
{
}

///  After rotation, the new image id is alive.
pub proof fn lemma_new_image_alive_after_rotate(
    images: Map<nat, ImageState>,
    old_image_id: nat,
    new_image_id: nat,
    image_template: ImageState,
)
    ensures
        acquire_rotate_images(images, old_image_id, new_image_id, image_template)
            .contains_key(new_image_id),
        acquire_rotate_images(images, old_image_id, new_image_id, image_template)
            [new_image_id].alive,
{
}

///  Rotation preserves all other images unchanged.
pub proof fn lemma_rotate_preserves_other_images(
    images: Map<nat, ImageState>,
    old_image_id: nat,
    new_image_id: nat,
    image_template: ImageState,
    other_id: nat,
)
    requires
        other_id != old_image_id,
        other_id != new_image_id,
        images.contains_key(other_id),
    ensures
        acquire_rotate_images(images, old_image_id, new_image_id, image_template)
            .contains_key(other_id),
        acquire_rotate_images(images, old_image_id, new_image_id, image_template)[other_id]
            == images[other_id],
{
}

} //  verus!
