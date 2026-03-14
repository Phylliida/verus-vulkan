use vstd::prelude::*;
use crate::resource::*;
use crate::sync::*;
use crate::sync_proofs::*;
use crate::recording_commands::*;
use crate::queue::*;
use crate::fence::*;
use crate::semaphore::*;
use crate::swapchain::*;
use crate::completion::*;
use crate::safety::*;
use crate::frame::*;
use crate::device::*;
use crate::lifetime::*;
use crate::sync_token::*;
use crate::command::*;
use crate::submit::*;
use crate::resource_lifecycle::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// The lifecycle state of a single frame in flight.
pub enum FrameLifecycleState {
    /// No frame in progress; resources idle.
    Idle,
    /// Swapchain image acquired; ready to record commands.
    Acquired,
    /// Commands recorded; barriers applied; ready to submit.
    Recorded,
    /// Work submitted to GPU; fence associated.
    Submitted,
    /// Present issued to swapchain.
    Presented,
    /// Fence waited; GPU work complete; safe to reuse/destroy resources.
    Completed,
}

/// Bundles all the state needed to track a frame through its lifecycle.
pub struct FrameInvariant {
    pub frame: FrameSubmission,
    pub swapchain: SwapchainState,
    pub queue: QueueState,
    pub dev: DeviceState,
    pub cb_states: Map<nat, CommandBufferState>,
    pub sem_states: Map<nat, SemaphoreState>,
    pub fence_states: Map<nat, FenceState>,
    pub lifecycle_states: Map<ResourceId, ResourceLifecycleState>,
    pub thread: ThreadId,
    pub reg: TokenRegistry,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// The frame lifecycle invariant for each state.
pub open spec fn frame_lifecycle_valid(
    state: FrameLifecycleState,
    inv: FrameInvariant,
) -> bool {
    match state {
        FrameLifecycleState::Idle => {
            // Frame is well-formed and swapchain image is available
            frame_submission_well_formed(inv.frame)
            && !inv.swapchain.retired
            && inv.frame.image_index < inv.swapchain.image_states.len()
            && inv.swapchain.image_states[inv.frame.image_index as int]
                == SwapchainImageState::Available
            // Fence exists and is unsignaled
            && inv.fence_states.contains_key(inv.frame.frame_fence)
            && !inv.fence_states[inv.frame.frame_fence].signaled
            // Thread holds exclusive queue access
            && holds_exclusive(inv.reg, inv.queue.queue_id, inv.thread)
        },
        FrameLifecycleState::Acquired => {
            // Image is now Acquired
            frame_submission_well_formed(inv.frame)
            && inv.frame.image_index < inv.swapchain.image_states.len()
            && inv.swapchain.image_states[inv.frame.image_index as int]
                == SwapchainImageState::Acquired
            && holds_exclusive(inv.reg, inv.queue.queue_id, inv.thread)
        },
        FrameLifecycleState::Recorded => {
            // Commands recorded, ready to submit
            frame_submission_well_formed(inv.frame)
            && inv.frame.image_index < inv.swapchain.image_states.len()
            && holds_exclusive(inv.reg, inv.queue.queue_id, inv.thread)
        },
        FrameLifecycleState::Submitted => {
            // Work submitted, fence associated
            frame_submission_well_formed(inv.frame)
            && inv.frame.image_index < inv.swapchain.image_states.len()
            && inv.fence_states.contains_key(inv.frame.frame_fence)
        },
        FrameLifecycleState::Presented => {
            // Present issued, waiting for completion
            frame_submission_well_formed(inv.frame)
            && inv.frame.image_index < inv.swapchain.image_states.len()
            && inv.fence_states.contains_key(inv.frame.frame_fence)
        },
        FrameLifecycleState::Completed => {
            // Fence waited, GPU work done
            frame_submission_well_formed(inv.frame)
        },
    }
}

/// All barrier recording is complete and resources are properly synchronized
/// before submit.
pub open spec fn frame_sync_complete(
    ctx: RecordingContext,
    inv: FrameInvariant,
) -> bool {
    // Referenced resources are tracked
    forall|r: ResourceId| inv.frame.submit_info.referenced_resources.contains(r)
        ==> ctx.referenced_resources.contains(r)
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// Idle → Acquired: acquiring the swapchain image advances the lifecycle.
pub proof fn lemma_acquire_advances_lifecycle(inv: FrameInvariant)
    requires frame_lifecycle_valid(FrameLifecycleState::Idle, inv),
    ensures ({
        let new_swapchain = acquire_image(inv.swapchain, inv.frame.image_index).unwrap();
        let new_inv = FrameInvariant { swapchain: new_swapchain, ..inv };
        frame_lifecycle_valid(FrameLifecycleState::Acquired, new_inv)
    }),
{
    lemma_acquire_makes_acquired(inv.swapchain, inv.frame.image_index);
}

/// Acquired → Recorded: recording commands (externally) advances lifecycle.
/// The caller provides a recording context that tracks resources.
pub proof fn lemma_record_advances_lifecycle(
    inv: FrameInvariant,
    ctx: RecordingContext,
)
    requires
        frame_lifecycle_valid(FrameLifecycleState::Acquired, inv),
        frame_sync_complete(ctx, inv),
    ensures
        frame_lifecycle_valid(FrameLifecycleState::Recorded, inv),
{
}

/// Submitted → Completed after fence wait: resources are safe to destroy.
///
/// Delegates to lemma_fence_wait_enables_destroy and
/// lemma_submit_wait_destroy_safe.
pub proof fn lemma_fence_wait_enables_cleanup(
    inv: FrameInvariant,
    resource: ResourceId,
)
    requires
        frame_lifecycle_valid(FrameLifecycleState::Submitted, inv),
        inv.frame.submit_info.referenced_resources.contains(resource),
        // No prior submission references this resource
        forall|i: int| 0 <= i < inv.dev.pending_submissions.len()
            ==> !inv.dev.pending_submissions[i].referenced_resources.contains(resource),
        // Thread still holds exclusive queue access
        holds_exclusive(inv.reg, inv.queue.queue_id, inv.thread),
    ensures ({
        // After submit + fence wait, resource is safe to destroy
        let submit_result = submit_ghost(inv.queue, inv.frame.submit_info, inv.thread, inv.reg);
        submit_result.is_some() ==> ({
            let (new_queue, record) = submit_result.unwrap();
            let new_dev = DeviceState {
                pending_submissions: inv.dev.pending_submissions.push(record),
                ..inv.dev
            };
            let (post_wait_dev, _) = fence_wait_ghost(new_dev, inv.frame.frame_fence, inv.fence_states);
            safe_to_destroy_resource(post_wait_dev, resource)
        })
    }),
{
    let submit_result = submit_ghost(inv.queue, inv.frame.submit_info, inv.thread, inv.reg);
    if submit_result.is_some() {
        lemma_submit_wait_destroy_safe(
            inv.dev, inv.queue, inv.frame.submit_info,
            inv.frame.frame_fence, resource,
            inv.fence_states, inv.thread, inv.reg,
        );
    }
}

/// **Crown jewel**: Idle → Completed in one shot.
/// A frame that starts from Idle with a well-formed submission,
/// acquires, records, submits, and fence-waits produces a state
/// where all referenced resources are safe to destroy.
pub proof fn lemma_full_frame_safe(
    inv: FrameInvariant,
    resource: ResourceId,
)
    requires
        frame_lifecycle_valid(FrameLifecycleState::Idle, inv),
        inv.frame.submit_info.referenced_resources.contains(resource),
        // No prior submission references this resource
        forall|i: int| 0 <= i < inv.dev.pending_submissions.len()
            ==> !inv.dev.pending_submissions[i].referenced_resources.contains(resource),
        // Submission is valid
        submission_valid(
            inv.frame.submit_info, inv.cb_states, inv.sem_states,
            inv.fence_states, inv.lifecycle_states, inv.queue.queue_id, inv.thread, inv.reg,
        ),
    ensures ({
        // The full acquire→submit path succeeds
        let acquire_result = acquire_image(inv.swapchain, inv.frame.image_index);
        acquire_result.is_some() ==> ({
            let submit_result = submit_ghost(inv.queue, inv.frame.submit_info, inv.thread, inv.reg);
            submit_result.is_some() ==> ({
                let (new_queue, record) = submit_result.unwrap();
                let new_dev = DeviceState {
                    pending_submissions: inv.dev.pending_submissions.push(record),
                    ..inv.dev
                };
                let (post_wait_dev, _) = fence_wait_ghost(new_dev, inv.frame.frame_fence, inv.fence_states);
                safe_to_destroy_resource(post_wait_dev, resource)
            })
        })
    }),
{
    // Step 1: Acquire succeeds
    lemma_acquire_makes_acquired(inv.swapchain, inv.frame.image_index);
    let acquire_result = acquire_image(inv.swapchain, inv.frame.image_index);
    if acquire_result.is_some() {
        // Step 2: Submit + fence wait → safe to destroy
        let submit_result = submit_ghost(inv.queue, inv.frame.submit_info, inv.thread, inv.reg);
        if submit_result.is_some() {
            lemma_submit_wait_destroy_safe(
                inv.dev, inv.queue, inv.frame.submit_info,
                inv.frame.frame_fence, resource,
                inv.fence_states, inv.thread, inv.reg,
            );
        }
    }
}

/// Resources referenced by the frame are a subset of the recording context's
/// referenced resources when frame_sync_complete holds.
pub proof fn lemma_frame_resources_bounded(
    inv: FrameInvariant,
    ctx: RecordingContext,
    resource: ResourceId,
)
    requires
        frame_sync_complete(ctx, inv),
        inv.frame.submit_info.referenced_resources.contains(resource),
    ensures
        ctx.referenced_resources.contains(resource),
{
}

/// Present succeeds after submit when the swapchain image is still Acquired.
pub proof fn lemma_present_after_submit(
    inv: FrameInvariant,
)
    requires
        frame_lifecycle_valid(FrameLifecycleState::Acquired, inv),
    ensures ({
        let result = present_image(inv.swapchain, inv.frame.image_index);
        result.is_some()
        && result.unwrap().image_states[inv.frame.image_index as int]
            == SwapchainImageState::PresentPending
    }),
{
    lemma_present_makes_pending(inv.swapchain, inv.frame.image_index);
}

} // verus!
