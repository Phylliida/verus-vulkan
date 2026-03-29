use vstd::prelude::*;
use crate::memory::*;

verus! {

///  Runtime wrapper for a Vulkan image.
pub struct RuntimeImage {
    ///  Opaque handle (maps to VkImage).
    pub handle: u64,
    ///  Ghost model of the image state.
    pub state: Ghost<ImageState>,
}

impl View for RuntimeImage {
    type V = ImageState;
    open spec fn view(&self) -> ImageState { self.state@ }
}

///  Well-formedness of the runtime image.
pub open spec fn runtime_image_wf(img: &RuntimeImage) -> bool {
    img@.alive
}

} //  verus!
