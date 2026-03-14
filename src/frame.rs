use vstd::prelude::*;
use crate::resource::*;
use crate::command::*;
use crate::lifetime::*;
use crate::device::*;
use crate::fence::*;
use crate::semaphore::*;
use crate::queue::*;
use crate::swapchain::*;
use crate::sync::*;
use crate::submit::*;
use crate::completion::*;
use crate::sync_token::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// Describes a complete frame submission: acquire image, submit work, present.
pub struct FrameSubmission {
    /// The swapchain image index to render to.
    pub image_index: nat,
    /// Semaphore signaled when acquire completes (GPU can start rendering).
    pub acquire_semaphore: nat,
    /// Semaphore signaled when rendering completes (presentation can begin).
    pub render_semaphore: nat,
    /// Fence signaled when the GPU finishes this frame's work.
    pub frame_fence: nat,
    /// The submit info for the rendering work.
    pub submit_info: SubmitInfo,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// A frame submission is well-formed:
/// - The submit info waits on the acquire semaphore.
/// - The submit info signals the render semaphore.
/// - The submit info uses the frame fence.
/// - The submit info is otherwise well-formed.
pub open spec fn frame_submission_well_formed(frame: FrameSubmission) -> bool {
    submit_info_well_formed(frame.submit_info)
    && frame.submit_info.fence_id == Some(frame.frame_fence)
    && frame.submit_info.wait_semaphores.len() >= 1
    && frame.submit_info.wait_semaphores[0] == frame.acquire_semaphore
    && frame.submit_info.signal_semaphores.len() >= 1
    && frame.submit_info.signal_semaphores[0] == frame.render_semaphore
}

/// The full acquire→submit ghost transition.
/// Returns updated (swapchain, queue, device, cb_states, sem_states, fence_states).
///
/// Requires the submitting thread to hold exclusive access to the queue.
pub open spec fn frame_acquire_and_submit(
    swapchain: SwapchainState,
    queue: QueueState,
    dev: DeviceState,
    frame: FrameSubmission,
    cb_states: Map<nat, CommandBufferState>,
    sem_states: Map<nat, SemaphoreState>,
    fence_states: Map<nat, FenceState>,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<(SwapchainState, QueueState, DeviceState, Map<nat, CommandBufferState>, Map<nat, SemaphoreState>, Map<nat, FenceState>)>
    recommends
        frame.submit_info.fence_id.is_some() ==> fence_states.contains_key(frame.submit_info.fence_id.unwrap()),
{
    // Step 1: Acquire the swapchain image
    match acquire_image(swapchain, frame.image_index) {
        None => None,
        Some(new_swapchain) => {
            // Step 2: Submit the rendering work (requires exclusive queue access)
            match submit_ghost(queue, frame.submit_info, thread, reg) {
                None => None,
                Some((new_queue, record)) => {
                    let new_dev = DeviceState {
                        pending_submissions: dev.pending_submissions.push(record),
                        ..dev
                    };
                    // Step 3: Transition CBs to pending
                    let new_cbs = transition_cbs_to_pending(
                        frame.submit_info.command_buffers, cb_states,
                    );
                    // Step 4: Consume wait semaphores
                    let new_sems = consume_wait_semaphores(
                        frame.submit_info.wait_semaphores, sem_states,
                    );
                    // Step 5: Mark fence as associated with this submission
                    let new_fences = match frame.submit_info.fence_id {
                        Some(fid) => fence_states.insert(
                            fid,
                            FenceState { submission_id: Some(record.id), ..fence_states[fid] },
                        ),
                        None => fence_states,
                    };
                    Some((new_swapchain, new_queue, new_dev, new_cbs, new_sems, new_fences))
                },
            }
        },
    }
}

/// Ghost transition for presenting a frame after rendering completes.
pub open spec fn frame_present(
    swapchain: SwapchainState,
    frame: FrameSubmission,
) -> Option<SwapchainState> {
    present_image(swapchain, frame.image_index)
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// A well-formed frame submission waits on the acquire semaphore.
pub proof fn lemma_frame_waits_on_acquire(frame: FrameSubmission)
    requires frame_submission_well_formed(frame),
    ensures
        frame.submit_info.wait_semaphores.len() >= 1,
        frame.submit_info.wait_semaphores[0] == frame.acquire_semaphore,
{
}

/// A well-formed frame submission signals the render semaphore.
pub proof fn lemma_frame_signals_render(frame: FrameSubmission)
    requires frame_submission_well_formed(frame),
    ensures
        frame.submit_info.signal_semaphores.len() >= 1,
        frame.submit_info.signal_semaphores[0] == frame.render_semaphore,
{
}

/// A well-formed frame submission uses a fence.
pub proof fn lemma_frame_uses_fence(frame: FrameSubmission)
    requires frame_submission_well_formed(frame),
    ensures frame.submit_info.fence_id == Some(frame.frame_fence),
{
}

/// If acquire succeeds, the swapchain image transitions to Acquired.
pub proof fn lemma_acquire_makes_acquired(
    swapchain: SwapchainState,
    idx: nat,
)
    requires
        !swapchain.retired,
        idx < swapchain.image_states.len(),
        swapchain.image_states[idx as int] == SwapchainImageState::Available,
    ensures ({
        let result = acquire_image(swapchain, idx);
        result.is_some()
        && result.unwrap().image_states[idx as int] == SwapchainImageState::Acquired
    }),
{
}

/// If present succeeds, the swapchain image transitions to PresentPending.
pub proof fn lemma_present_makes_pending(
    swapchain: SwapchainState,
    idx: nat,
)
    requires
        idx < swapchain.image_states.len(),
        swapchain.image_states[idx as int] == SwapchainImageState::Acquired,
    ensures ({
        let result = present_image(swapchain, idx);
        result.is_some()
        && result.unwrap().image_states[idx as int] == SwapchainImageState::PresentPending
    }),
{
}

/// The full acquire→present cycle returns the image to PresentPending.
pub proof fn lemma_acquire_present_cycle(
    swapchain: SwapchainState,
    idx: nat,
)
    requires
        !swapchain.retired,
        idx < swapchain.image_states.len(),
        swapchain.image_states[idx as int] == SwapchainImageState::Available,
    ensures ({
        let after_acquire = acquire_image(swapchain, idx).unwrap();
        let after_present = present_image(after_acquire, idx);
        after_present.is_some()
        && after_present.unwrap().image_states[idx as int] == SwapchainImageState::PresentPending
    }),
{
    let after_acquire = acquire_image(swapchain, idx).unwrap();
}

/// After present_complete, the image returns to Available.
pub proof fn lemma_full_frame_cycle(
    swapchain: SwapchainState,
    idx: nat,
)
    requires
        !swapchain.retired,
        idx < swapchain.image_states.len(),
        swapchain.image_states[idx as int] == SwapchainImageState::Available,
    ensures ({
        let s1 = acquire_image(swapchain, idx).unwrap();
        let s2 = present_image(s1, idx).unwrap();
        let s3 = present_complete(s2, idx);
        s3.is_some()
        && s3.unwrap().image_states[idx as int] == SwapchainImageState::Available
    }),
{
}

} // verus!
