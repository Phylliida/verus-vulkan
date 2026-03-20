use vstd::prelude::*;

verus! {

/// Swapchain image metadata extracted at creation time.
/// Used to construct `ImageState` templates without repeating format/size/usage.
pub struct SwapchainImageInfo {
    pub format: nat,
    pub width: nat,
    pub height: nat,
    pub usage: Set<nat>,
}

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
    /// Whether this swapchain has been retired (replaced by a new swapchain).
    /// Acquiring from a retired swapchain is UB.
    pub retired: bool,
    /// Whether this swapchain has not been destroyed.
    pub alive: bool,
    /// Logical image identity per swapchain index. On acquire, the id at the
    /// acquired index is rotated to a fresh value so that descriptors bound to
    /// the old id become stale (their `descriptor_binding_resource_alive` check
    /// against the caller's `images` map will fail).
    pub current_image_ids: Seq<nat>,
    /// Monotonic counter for generating unique image ids.
    pub next_image_id: nat,
    /// Image metadata for constructing ImageState templates.
    pub image_info: SwapchainImageInfo,
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

/// Acquire image at index `idx`. Fails if swapchain is retired or destroyed.
/// On success, the image at `idx` transitions to Acquired and its logical
/// image id is rotated to `next_image_id` (invalidating stale descriptors).
pub open spec fn acquire_image(swapchain: SwapchainState, idx: nat) -> Option<SwapchainState>
    recommends idx < swapchain.image_states.len(),
{
    if !swapchain.alive || swapchain.retired {
        None
    } else if idx >= swapchain.image_states.len() {
        None
    } else {
        match swapchain.image_states[idx as int] {
            SwapchainImageState::Available => Some(SwapchainState {
                image_states: swapchain.image_states.update(idx as int, SwapchainImageState::Acquired),
                current_image_ids: swapchain.current_image_ids.update(idx as int, swapchain.next_image_id),
                next_image_id: swapchain.next_image_id + 1,
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

/// Retire a swapchain (marks it as replaced by a new swapchain).
pub open spec fn retire_swapchain(swapchain: SwapchainState) -> SwapchainState {
    SwapchainState { retired: true, ..swapchain }
}

/// Ghost update: destroy the swapchain.
pub open spec fn destroy_swapchain_ghost(swapchain: SwapchainState) -> SwapchainState
    recommends swapchain.alive,
{
    SwapchainState { alive: false, ..swapchain }
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

/// Acquiring an available image from a live, non-retired swapchain succeeds.
pub proof fn lemma_acquire_available_succeeds(swapchain: SwapchainState, idx: nat)
    requires
        swapchain.alive,
        !swapchain.retired,
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
        swapchain.alive,
        !swapchain.retired,
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
        swapchain.alive,
        !swapchain.retired,
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
        swapchain.alive,
        !swapchain.retired,
        idx < swapchain.image_states.len(),
        other < swapchain.image_states.len(),
        idx != other,
        swapchain.image_states[idx as int] == SwapchainImageState::Available,
    ensures
        acquire_image(swapchain, idx).unwrap().image_states[other as int]
            == swapchain.image_states[other as int],
{
}

/// A retired swapchain always returns None from acquire_image.
pub proof fn lemma_retired_cannot_acquire(swapchain: SwapchainState, idx: nat)
    requires swapchain.retired,
    ensures acquire_image(swapchain, idx).is_none(),
{
}

/// A destroyed swapchain always returns None from acquire_image.
pub proof fn lemma_destroyed_cannot_acquire(swapchain: SwapchainState, idx: nat)
    requires !swapchain.alive,
    ensures acquire_image(swapchain, idx).is_none(),
{
}

/// Destroying preserves ID and image states.
pub proof fn lemma_destroy_preserves_identity(swapchain: SwapchainState)
    ensures
        destroy_swapchain_ghost(swapchain).id == swapchain.id,
        destroy_swapchain_ghost(swapchain).image_states == swapchain.image_states,
        !destroy_swapchain_ghost(swapchain).alive,
{
}

/// Retiring a swapchain preserves its image states (in-flight images
/// can still be presented/completed).
pub proof fn lemma_retire_preserves_images(swapchain: SwapchainState)
    ensures
        retire_swapchain(swapchain).image_states == swapchain.image_states,
        retire_swapchain(swapchain).id == swapchain.id,
{
}

// ── Image-id rotation lemmas ─────────────────────────────────────────

/// After acquire at `idx`, the image id at `idx` equals the old `next_image_id`.
pub proof fn lemma_acquire_rotates_image_id(swapchain: SwapchainState, idx: nat)
    requires
        swapchain.alive,
        !swapchain.retired,
        idx < swapchain.image_states.len(),
        swapchain.image_states[idx as int] == SwapchainImageState::Available,
        swapchain.current_image_ids.len() == swapchain.image_states.len(),
    ensures
        acquire_image(swapchain, idx).unwrap().current_image_ids[idx as int]
            == swapchain.next_image_id,
{
}

/// Acquire at `idx` preserves image ids at other indices.
pub proof fn lemma_acquire_preserves_other_ids(
    swapchain: SwapchainState, idx: nat, j: nat,
)
    requires
        swapchain.alive,
        !swapchain.retired,
        idx < swapchain.image_states.len(),
        j < swapchain.image_states.len(),
        idx != j,
        swapchain.image_states[idx as int] == SwapchainImageState::Available,
        swapchain.current_image_ids.len() == swapchain.image_states.len(),
    ensures
        acquire_image(swapchain, idx).unwrap().current_image_ids[j as int]
            == swapchain.current_image_ids[j as int],
{
}

/// The new image id differs from all current image ids (by monotonicity).
/// Requires that all current ids are less than `next_image_id`.
pub proof fn lemma_acquire_new_id_unique(
    swapchain: SwapchainState, idx: nat,
)
    requires
        swapchain.alive,
        !swapchain.retired,
        idx < swapchain.image_states.len(),
        swapchain.image_states[idx as int] == SwapchainImageState::Available,
        swapchain.current_image_ids.len() == swapchain.image_states.len(),
        forall|j: int| 0 <= j < swapchain.current_image_ids.len() ==>
            swapchain.current_image_ids[j] < swapchain.next_image_id,
    ensures ({
        let new_sc = acquire_image(swapchain, idx).unwrap();
        forall|j: int| 0 <= j < new_sc.current_image_ids.len() ==>
            new_sc.current_image_ids[j] < new_sc.next_image_id
    }),
{
    let new_sc = acquire_image(swapchain, idx).unwrap();
    assert forall|j: int| 0 <= j < new_sc.current_image_ids.len()
    implies new_sc.current_image_ids[j] < new_sc.next_image_id by {
        if j == idx as int {
            // new id = old next_image_id < old next_image_id + 1 = new next_image_id
        } else {
            // preserved id < old next_image_id < new next_image_id
        }
    }
}

/// Acquire preserves the length of current_image_ids.
pub proof fn lemma_acquire_preserves_image_ids_len(swapchain: SwapchainState, idx: nat)
    requires
        swapchain.alive,
        !swapchain.retired,
        idx < swapchain.image_states.len(),
        swapchain.image_states[idx as int] == SwapchainImageState::Available,
        swapchain.current_image_ids.len() == swapchain.image_states.len(),
    ensures
        acquire_image(swapchain, idx).unwrap().current_image_ids.len()
            == swapchain.current_image_ids.len(),
{
}

} // verus!
