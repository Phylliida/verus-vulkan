use vstd::prelude::*;

verus! {

///  Ghost token proving the event loop has exited.
///
///  `vk_destroy_swapchain` and `vk_destroy_surface` require this permit,
///  preventing callers from destroying window-bound resources inside an
///  event handler (which crashes MoltenVK / causes use-after-free).
pub struct WindowCleanupPermit {
    pub event_loop_exited: bool,
}

pub open spec fn cleanup_permit_valid(p: WindowCleanupPermit) -> bool {
    p.event_loop_exited
}

} //  verus!
