use vstd::prelude::*;
use crate::swapchain::*;
use crate::image_layout::ImageLayout;
use crate::resource::ResourceId;
use crate::sync_token::*;
use super::image_layout::RuntimeImageLayoutTracker;

verus! {

/// Runtime wrapper for a Vulkan swapchain.
pub struct RuntimeSwapchain {
    /// Opaque handle (maps to VkSwapchainKHR).
    pub handle: u64,
    /// Ghost model of the swapchain state.
    pub state: Ghost<SwapchainState>,
}

impl View for RuntimeSwapchain {
    type V = SwapchainState;
    open spec fn view(&self) -> SwapchainState { self.state@ }
}

/// Well-formedness of the runtime swapchain.
pub open spec fn runtime_swapchain_wf(sc: &RuntimeSwapchain) -> bool {
    sc@.image_states.len() > 0
}

/// Number of images in the swapchain.
pub open spec fn swapchain_image_count(sc: &RuntimeSwapchain) -> nat {
    sc@.image_states.len()
}

/// Number of currently acquired images.
pub open spec fn swapchain_acquired_count(sc: &RuntimeSwapchain) -> nat {
    count_acquired(sc@)
}

/// Number of present-pending images.
pub open spec fn swapchain_present_pending_count(sc: &RuntimeSwapchain) -> nat {
    count_present_pending(sc@)
}

/// Total in-flight images (acquired + present-pending).
pub open spec fn swapchain_in_flight_count(sc: &RuntimeSwapchain) -> nat {
    count_in_flight(sc@)
}

/// Whether the swapchain has any available images to acquire.
pub open spec fn swapchain_has_available(sc: &RuntimeSwapchain) -> bool {
    exists|i: int| 0 <= i < sc@.image_states.len()
        && sc@.image_states[i] == SwapchainImageState::Available
}

/// All images are currently in Available state.
pub open spec fn swapchain_all_available(sc: &RuntimeSwapchain) -> bool {
    all_available(sc@)
}

/// Swapchain ID.
pub open spec fn swapchain_id(sc: &RuntimeSwapchain) -> nat {
    sc@.id
}

/// Whether a specific image can be acquired.
pub open spec fn can_acquire_image(sc: &RuntimeSwapchain, idx: nat) -> bool {
    idx < sc@.image_states.len()
    && sc@.image_states[idx as int] == SwapchainImageState::Available
}

/// Whether a specific image can be presented.
pub open spec fn can_present_image(sc: &RuntimeSwapchain, idx: nat) -> bool {
    idx < sc@.image_states.len()
    && sc@.image_states[idx as int] == SwapchainImageState::Acquired
}

/// Exec: create a swapchain with all images initially available.
pub fn create_swapchain_exec(
    handle: u64,
    id: Ghost<nat>,
    image_count: u64,
) -> (out: RuntimeSwapchain)
    requires image_count > 0,
    ensures
        runtime_swapchain_wf(&out),
        out@.id == id@,
        out@.image_states.len() == image_count as nat,
        all_available(out@),
{
    let ghost states = Seq::new(image_count as nat, |_i: int| SwapchainImageState::Available);
    RuntimeSwapchain {
        handle,
        state: Ghost(SwapchainState {
            id: id@,
            image_states: states,
        }),
    }
}

/// Exec: acquire the next available image at index `idx`.
/// Caller must prove exclusive access to the swapchain.
pub fn acquire_next_image_exec(
    sc: &mut RuntimeSwapchain,
    idx: u64,
    thread: Ghost<ThreadId>,
    reg: Ghost<TokenRegistry>,
)
    requires
        runtime_swapchain_wf(&*old(sc)),
        can_acquire_image(&*old(sc), idx as nat),
        holds_exclusive(reg@, old(sc)@.id, thread@),
    ensures
        sc@ == acquire_image(old(sc)@, idx as nat).unwrap(),
        sc@.image_states[idx as int] == SwapchainImageState::Acquired,
        sc@.image_states.len() == old(sc)@.image_states.len(),
{
    sc.state = Ghost(acquire_image(sc.state@, idx as nat).unwrap());
}

/// Exec: present the image at index `idx`.
/// Caller must prove the image is in PresentSrc layout via their layout tracker.
/// Requires exclusive access to both the swapchain and the presentation queue.
pub fn present_exec(
    sc: &mut RuntimeSwapchain,
    idx: u64,
    layout_tracker: &RuntimeImageLayoutTracker,
    image_resource: Ghost<ResourceId>,
    thread: Ghost<ThreadId>,
    queue_id: Ghost<nat>,
    reg: Ghost<TokenRegistry>,
)
    requires
        runtime_swapchain_wf(&*old(sc)),
        can_present_image(&*old(sc), idx as nat),
        layout_tracker@.contains_key(image_resource@),
        layout_tracker@[image_resource@] == ImageLayout::PresentSrc,
        holds_exclusive(reg@, old(sc)@.id, thread@),
        holds_exclusive(reg@, queue_id@, thread@),
    ensures
        sc@ == present_image(old(sc)@, idx as nat).unwrap(),
        sc@.image_states[idx as int] == SwapchainImageState::PresentPending,
        sc@.image_states.len() == old(sc)@.image_states.len(),
{
    sc.state = Ghost(present_image(sc.state@, idx as nat).unwrap());
}

/// Exec: mark a present-pending image as available (presentation completed).
/// Caller must prove exclusive access to the swapchain.
pub fn present_complete_exec(
    sc: &mut RuntimeSwapchain,
    idx: u64,
    thread: Ghost<ThreadId>,
    reg: Ghost<TokenRegistry>,
)
    requires
        runtime_swapchain_wf(&*old(sc)),
        idx < old(sc)@.image_states.len(),
        old(sc)@.image_states[idx as int] == SwapchainImageState::PresentPending,
        holds_exclusive(reg@, old(sc)@.id, thread@),
    ensures
        sc@ == present_complete(old(sc)@, idx as nat).unwrap(),
        sc@.image_states[idx as int] == SwapchainImageState::Available,
        sc@.image_states.len() == old(sc)@.image_states.len(),
{
    sc.state = Ghost(present_complete(sc.state@, idx as nat).unwrap());
}

/// Exec: get image count (queries the driver).
#[verifier::external_body]
pub fn get_swapchain_image_count_exec(sc: &RuntimeSwapchain) -> (out: u64)
    requires
        runtime_swapchain_wf(sc),
        sc@.image_states.len() <= u64::MAX as nat,
    ensures out as nat == sc@.image_states.len(),
{
    unimplemented!()
}

/// Exec: recreate swapchain with new image count (all images reset to Available).
/// Caller must prove no images are in-flight (all Available) and exclusive access.
pub fn recreate_swapchain_exec(
    sc: &mut RuntimeSwapchain,
    new_image_count: u64,
    thread: Ghost<ThreadId>,
    reg: Ghost<TokenRegistry>,
) -> (success: bool)
    requires
        runtime_swapchain_wf(&*old(sc)),
        new_image_count > 0,
        all_available(old(sc)@),
        holds_exclusive(reg@, old(sc)@.id, thread@),
    ensures
        success ==> (
            sc@.id == old(sc)@.id
            && sc@.image_states.len() == new_image_count as nat
            && all_available(sc@)
        ),
        !success ==> sc@ == old(sc)@,
{
    let ghost new_states = Seq::new(new_image_count as nat, |_i: int| SwapchainImageState::Available);
    sc.state = Ghost(SwapchainState {
        id: sc.state@.id,
        image_states: new_states,
    });
    true
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// Creating a swapchain gives a well-formed result.
pub proof fn lemma_create_swapchain_wf(id: nat, image_count: nat)
    requires image_count > 0,
    ensures ({
        let states = Seq::new(image_count, |_i: int| SwapchainImageState::Available);
        let sc = SwapchainState { id, image_states: states };
        sc.image_states.len() > 0
        && all_available(sc)
    }),
{
}

/// Acquiring a valid image succeeds (delegates to spec lemma).
pub proof fn lemma_acquire_valid(sc: &RuntimeSwapchain, idx: nat)
    requires
        runtime_swapchain_wf(sc),
        can_acquire_image(sc, idx),
    ensures
        acquire_image(sc@, idx).is_some(),
{
    lemma_acquire_available_succeeds(sc@, idx);
}

/// Presenting a valid image succeeds.
pub proof fn lemma_present_valid(sc: &RuntimeSwapchain, idx: nat)
    requires
        runtime_swapchain_wf(sc),
        can_present_image(sc, idx),
    ensures
        present_image(sc@, idx).is_some(),
{
}

/// Full roundtrip: acquire → present → complete returns to Available.
pub proof fn lemma_acquire_present_roundtrip(sc: &RuntimeSwapchain, idx: nat)
    requires
        runtime_swapchain_wf(sc),
        can_acquire_image(sc, idx),
    ensures ({
        let s1 = acquire_image(sc@, idx).unwrap();
        let s2 = present_image(s1, idx).unwrap();
        let s3 = present_complete(s2, idx).unwrap();
        s3.image_states[idx as int] == SwapchainImageState::Available
    }),
{
    lemma_full_cycle_returns_available(sc@, idx);
}

/// Image count is bounded by in-flight.
pub proof fn lemma_acquired_leq_total(sc: &RuntimeSwapchain)
    requires runtime_swapchain_wf(sc),
    ensures
        swapchain_acquired_count(sc) <= swapchain_image_count(sc),
{
    lemma_acquired_leq_total_helper(sc@.image_states, 0);
}

proof fn lemma_acquired_leq_total_helper(states: Seq<SwapchainImageState>, start: nat)
    requires start <= states.len(),
    ensures count_acquired_helper(states, start) + start <= states.len(),
    decreases states.len() - start,
{
    if start < states.len() {
        lemma_acquired_leq_total_helper(states, start + 1);
    }
}

/// Present-pending count is bounded by total.
pub proof fn lemma_present_pending_leq_total(sc: &RuntimeSwapchain)
    requires runtime_swapchain_wf(sc),
    ensures
        swapchain_present_pending_count(sc) <= swapchain_image_count(sc),
{
    lemma_present_pending_leq_total_helper(sc@.image_states, 0);
}

proof fn lemma_present_pending_leq_total_helper(states: Seq<SwapchainImageState>, start: nat)
    requires start <= states.len(),
    ensures count_present_pending_helper(states, start) + start <= states.len(),
    decreases states.len() - start,
{
    if start < states.len() {
        lemma_present_pending_leq_total_helper(states, start + 1);
    }
}

/// In-flight count is bounded: acquired ≤ total and present_pending ≤ total.
pub proof fn lemma_in_flight_bounded(sc: &RuntimeSwapchain)
    requires runtime_swapchain_wf(sc),
    ensures
        swapchain_acquired_count(sc) <= swapchain_image_count(sc),
        swapchain_present_pending_count(sc) <= swapchain_image_count(sc),
{
    lemma_acquired_leq_total(sc);
    lemma_present_pending_leq_total(sc);
}

/// Acquire preserves other images.
pub proof fn lemma_acquire_preserves_other(sc: &RuntimeSwapchain, idx: nat, other: nat)
    requires
        runtime_swapchain_wf(sc),
        can_acquire_image(sc, idx),
        other < sc@.image_states.len(),
        idx != other,
    ensures
        acquire_image(sc@, idx).unwrap().image_states[other as int]
            == sc@.image_states[other as int],
{
    crate::swapchain::lemma_acquire_preserves_other(sc@, idx, other);
}

/// Recreate preserves the swapchain ID, resets all images to Available,
/// and the result is well-formed.
pub proof fn lemma_recreate_preserves_id(
    old_sc: SwapchainState,
    new_image_count: nat,
)
    requires new_image_count > 0,
    ensures ({
        let new_states = Seq::new(new_image_count, |_i: int| SwapchainImageState::Available);
        let new_sc = SwapchainState { id: old_sc.id, image_states: new_states };
        new_sc.id == old_sc.id
        && new_sc.image_states.len() == new_image_count
        && new_sc.image_states.len() > 0
        && all_available(new_sc)
    }),
{
}

} // verus!
