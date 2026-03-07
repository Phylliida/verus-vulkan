use vstd::prelude::*;

verus! {

/// Lifecycle state of a single swapchain image.
pub enum SwapchainImageState {
    /// Available for acquisition via vkAcquireNextImageKHR.
    Available,
    /// Acquired by the application; being rendered to.
    Acquired,
    /// Submitted for presentation via vkQueuePresentKHR.
    PresentPending,
}

/// A swapchain with N images, each in some lifecycle state.
pub struct SwapchainState {
    /// Unique identifier for this swapchain (used for thread-safe sync token lookup).
    pub id: nat,
    pub image_states: Seq<SwapchainImageState>,
}

/// Count how many images are currently acquired (not available, not presenting).
pub open spec fn count_acquired(swapchain: SwapchainState) -> nat
    decreases swapchain.image_states.len(),
{
    count_acquired_helper(swapchain.image_states, 0)
}

/// Helper: count acquired images starting from index `start`.
pub open spec fn count_acquired_helper(states: Seq<SwapchainImageState>, start: nat) -> nat
    decreases states.len() - start,
{
    if start >= states.len() {
        0
    } else {
        let rest = count_acquired_helper(states, start + 1);
        match states[start as int] {
            SwapchainImageState::Acquired => 1 + rest,
            _ => rest,
        }
    }
}

/// Count images currently submitted for presentation.
pub open spec fn count_present_pending(swapchain: SwapchainState) -> nat {
    count_present_pending_helper(swapchain.image_states, 0)
}

/// Helper: count present-pending images starting from index `start`.
pub open spec fn count_present_pending_helper(states: Seq<SwapchainImageState>, start: nat) -> nat
    decreases states.len() - start,
{
    if start >= states.len() {
        0
    } else {
        let rest = count_present_pending_helper(states, start + 1);
        match states[start as int] {
            SwapchainImageState::PresentPending => 1 + rest,
            _ => rest,
        }
    }
}

/// Total in-flight images = acquired + present-pending.
pub open spec fn count_in_flight(swapchain: SwapchainState) -> nat {
    count_acquired(swapchain) + count_present_pending(swapchain)
}

/// Acquire image at index `idx`.
pub open spec fn acquire_image(swapchain: SwapchainState, idx: nat) -> Option<SwapchainState>
    recommends idx < swapchain.image_states.len(),
{
    if idx >= swapchain.image_states.len() {
        None
    } else {
        match swapchain.image_states[idx as int] {
            SwapchainImageState::Available => Some(SwapchainState {
                image_states: swapchain.image_states.update(idx as int, SwapchainImageState::Acquired),
                ..swapchain
            }),
            _ => None,
        }
    }
}

/// Present image at index `idx`.
pub open spec fn present_image(swapchain: SwapchainState, idx: nat) -> Option<SwapchainState>
    recommends idx < swapchain.image_states.len(),
{
    if idx >= swapchain.image_states.len() {
        None
    } else {
        match swapchain.image_states[idx as int] {
            SwapchainImageState::Acquired => Some(SwapchainState {
                image_states: swapchain.image_states.update(idx as int, SwapchainImageState::PresentPending),
                ..swapchain
            }),
            _ => None,
        }
    }
}

/// Image becomes available again after presentation completes.
pub open spec fn present_complete(swapchain: SwapchainState, idx: nat) -> Option<SwapchainState>
    recommends idx < swapchain.image_states.len(),
{
    if idx >= swapchain.image_states.len() {
        None
    } else {
        match swapchain.image_states[idx as int] {
            SwapchainImageState::PresentPending => Some(SwapchainState {
                image_states: swapchain.image_states.update(idx as int, SwapchainImageState::Available),
                ..swapchain
            }),
            _ => None,
        }
    }
}

/// A swapchain where all images are Available.
pub open spec fn all_available(swapchain: SwapchainState) -> bool {
    forall|i: int| 0 <= i < swapchain.image_states.len() ==>
        swapchain.image_states[i] == SwapchainImageState::Available
}

/// If all images are available, in-flight count is zero.
pub proof fn lemma_all_available_zero_in_flight(swapchain: SwapchainState)
    requires all_available(swapchain),
    ensures count_in_flight(swapchain) == 0,
    decreases swapchain.image_states.len(),
{
    lemma_all_available_zero_acquired(swapchain.image_states, 0);
    lemma_all_available_zero_present(swapchain.image_states, 0);
}

proof fn lemma_all_available_zero_acquired(states: Seq<SwapchainImageState>, start: nat)
    requires forall|i: int| 0 <= i < states.len() ==> states[i] == SwapchainImageState::Available,
    ensures count_acquired_helper(states, start) == 0,
    decreases states.len() - start,
{
    if start < states.len() {
        lemma_all_available_zero_acquired(states, start + 1);
    }
}

proof fn lemma_all_available_zero_present(states: Seq<SwapchainImageState>, start: nat)
    requires forall|i: int| 0 <= i < states.len() ==> states[i] == SwapchainImageState::Available,
    ensures count_present_pending_helper(states, start) == 0,
    decreases states.len() - start,
{
    if start < states.len() {
        lemma_all_available_zero_present(states, start + 1);
    }
}

} // verus!
