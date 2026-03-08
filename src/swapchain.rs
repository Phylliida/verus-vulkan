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

/// Acquiring an available image succeeds.
pub proof fn lemma_acquire_available_succeeds(swapchain: SwapchainState, idx: nat)
    requires
        idx < swapchain.image_states.len(),
        swapchain.image_states[idx as int] == SwapchainImageState::Available,
    ensures acquire_image(swapchain, idx).is_some(),
{
}

/// Acquiring a non-available image fails.
pub proof fn lemma_acquire_non_available_fails(swapchain: SwapchainState, idx: nat)
    requires
        idx < swapchain.image_states.len(),
        swapchain.image_states[idx as int] != SwapchainImageState::Available,
    ensures acquire_image(swapchain, idx).is_none(),
{
}

/// Presenting a non-acquired image fails.
pub proof fn lemma_present_non_acquired_fails(swapchain: SwapchainState, idx: nat)
    requires
        idx < swapchain.image_states.len(),
        swapchain.image_states[idx as int] != SwapchainImageState::Acquired,
    ensures present_image(swapchain, idx).is_none(),
{
}

/// Present complete on non-pending image fails.
pub proof fn lemma_complete_non_pending_fails(swapchain: SwapchainState, idx: nat)
    requires
        idx < swapchain.image_states.len(),
        swapchain.image_states[idx as int] != SwapchainImageState::PresentPending,
    ensures present_complete(swapchain, idx).is_none(),
{
}

/// Acquiring preserves the number of images.
pub proof fn lemma_acquire_preserves_image_count(swapchain: SwapchainState, idx: nat)
    requires
        idx < swapchain.image_states.len(),
        swapchain.image_states[idx as int] == SwapchainImageState::Available,
    ensures acquire_image(swapchain, idx).unwrap().image_states.len()
        == swapchain.image_states.len(),
{
}

/// Presenting preserves the number of images.
pub proof fn lemma_present_preserves_image_count(swapchain: SwapchainState, idx: nat)
    requires
        idx < swapchain.image_states.len(),
        swapchain.image_states[idx as int] == SwapchainImageState::Acquired,
    ensures present_image(swapchain, idx).unwrap().image_states.len()
        == swapchain.image_states.len(),
{
}

/// Full cycle: acquire → present → complete returns to Available.
pub proof fn lemma_full_cycle_returns_available(swapchain: SwapchainState, idx: nat)
    requires
        idx < swapchain.image_states.len(),
        swapchain.image_states[idx as int] == SwapchainImageState::Available,
    ensures ({
        let s1 = acquire_image(swapchain, idx).unwrap();
        let s2 = present_image(s1, idx).unwrap();
        let s3 = present_complete(s2, idx).unwrap();
        s3.image_states[idx as int] == SwapchainImageState::Available
    }),
{
}

/// Operations on index `idx` don't affect other images.
pub proof fn lemma_acquire_preserves_other(
    swapchain: SwapchainState, idx: nat, other: nat,
)
    requires
        idx < swapchain.image_states.len(),
        other < swapchain.image_states.len(),
        idx != other,
        swapchain.image_states[idx as int] == SwapchainImageState::Available,
    ensures
        acquire_image(swapchain, idx).unwrap().image_states[other as int]
            == swapchain.image_states[other as int],
{
}

} // verus!
