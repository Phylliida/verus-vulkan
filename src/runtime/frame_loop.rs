use vstd::prelude::*;

verus! {

use crate::resource::*;
use crate::sync::*;
use crate::recording_commands::*;
use crate::frame::*;
use crate::frame_lifecycle::*;
use crate::swapchain::*;
use crate::queue::*;
use crate::device::*;
use crate::fence::*;
use crate::semaphore::*;
use crate::command::*;
use crate::completion::*;
use crate::lifetime::*;
use crate::pool_ownership::*;
use crate::sync_token::*;
use crate::runtime::command_buffer::*;

//  ─── Types ─────────────────────────────────────────────────────

///  Runtime frame state: tracks the lifecycle of a single frame in flight.
pub struct RuntimeFrameState {
    pub lifecycle: Ghost<FrameLifecycleState>,
    pub frame: Ghost<FrameSubmission>,
    pub image_index: u64,
}

//  ─── Spec functions ────────────────────────────────────────────

///  Well-formedness of the runtime frame state.
pub open spec fn frame_state_wf(
    fs: &RuntimeFrameState,
    inv: FrameInvariant,
) -> bool {
    frame_lifecycle_valid(fs.lifecycle@, inv)
    && fs.frame@ == inv.frame
    && fs.image_index as nat == inv.frame.image_index
}

///  Frame is idle and ready to begin.
pub open spec fn frame_is_idle(fs: &RuntimeFrameState) -> bool {
    fs.lifecycle@ == FrameLifecycleState::Idle
}

///  Frame has completed (fence waited).
pub open spec fn frame_is_completed(fs: &RuntimeFrameState) -> bool {
    fs.lifecycle@ == FrameLifecycleState::Completed
}

//  ─── Exec functions ────────────────────────────────────────────

///  Begin a frame: acquire swapchain image. Idle → Acquired.
pub fn frame_begin_exec(
    fs: &mut RuntimeFrameState,
    inv: Ghost<FrameInvariant>,
)
    requires
        frame_state_wf(&*old(fs), inv@),
        frame_is_idle(&*old(fs)),
    ensures
        fs.lifecycle@ == FrameLifecycleState::Acquired,
        fs.frame@ == old(fs).frame@,
        fs.image_index == old(fs).image_index,
{
    proof {
        lemma_acquire_advances_lifecycle(inv@);
    }
    fs.lifecycle = Ghost(FrameLifecycleState::Acquired);
}

///  Submit recorded commands. Acquired+Recorded → Submitted.
///  Caller must have recorded commands and established sync.
pub fn frame_submit_exec(
    fs: &mut RuntimeFrameState,
    inv: Ghost<FrameInvariant>,
    ctx: Ghost<RecordingContext>,
)
    requires
        frame_state_wf(&*old(fs), inv@),
        old(fs).lifecycle@ == FrameLifecycleState::Acquired,
        frame_sync_complete(ctx@, inv@),
    ensures
        fs.lifecycle@ == FrameLifecycleState::Submitted,
        fs.frame@ == old(fs).frame@,
        fs.image_index == old(fs).image_index,
{
    proof {
        lemma_record_advances_lifecycle(inv@, ctx@);
    }
    fs.lifecycle = Ghost(FrameLifecycleState::Submitted);
}

///  Present the swapchain image. Submitted → Presented.
pub fn frame_present_exec(
    fs: &mut RuntimeFrameState,
    inv: Ghost<FrameInvariant>,
)
    requires
        frame_state_wf(&*old(fs), inv@),
        old(fs).lifecycle@ == FrameLifecycleState::Submitted,
    ensures
        fs.lifecycle@ == FrameLifecycleState::Presented,
        fs.frame@ == old(fs).frame@,
        fs.image_index == old(fs).image_index,
{
    fs.lifecycle = Ghost(FrameLifecycleState::Presented);
}

///  Wait on fence. Presented/Submitted → Completed.
pub fn frame_wait_exec(
    fs: &mut RuntimeFrameState,
    inv: Ghost<FrameInvariant>,
)
    requires
        frame_state_wf(&*old(fs), inv@),
        old(fs).lifecycle@ == FrameLifecycleState::Presented
            || old(fs).lifecycle@ == FrameLifecycleState::Submitted,
    ensures
        fs.lifecycle@ == FrameLifecycleState::Completed,
        fs.frame@ == old(fs).frame@,
        fs.image_index == old(fs).image_index,
{
    fs.lifecycle = Ghost(FrameLifecycleState::Completed);
}

//  ─── Proof functions ───────────────────────────────────────────

///  Acquire advances from Idle to Acquired.
pub proof fn lemma_begin_advances(
    fs: RuntimeFrameState,
    inv: FrameInvariant,
)
    requires
        frame_state_wf(&fs, inv),
        frame_is_idle(&fs),
    ensures
        frame_lifecycle_valid(FrameLifecycleState::Acquired, FrameInvariant {
            swapchain: acquire_image(inv.swapchain, inv.frame.image_index).unwrap(),
            ..inv
        }),
{
    lemma_acquire_advances_lifecycle(inv);
}

///  Submit advances from Recorded to Submitted.
pub proof fn lemma_submit_advances(
    fs: RuntimeFrameState,
    inv: FrameInvariant,
    ctx: RecordingContext,
)
    requires
        frame_state_wf(&fs, inv),
        fs.lifecycle@ == FrameLifecycleState::Acquired,
        frame_sync_complete(ctx, inv),
    ensures
        frame_lifecycle_valid(FrameLifecycleState::Recorded, inv),
{
    lemma_record_advances_lifecycle(inv, ctx);
}

///  Present advances from Submitted.
pub proof fn lemma_present_advances(
    fs: RuntimeFrameState,
    inv: FrameInvariant,
)
    requires
        frame_state_wf(&fs, inv),
        fs.lifecycle@ == FrameLifecycleState::Acquired,
    ensures
        ({
            let result = present_image(inv.swapchain, inv.frame.image_index);
            result.is_some()
        }),
{
    lemma_present_after_submit(inv);
}

///  **Crown jewel**: A full frame loop (begin → submit → present → wait) produces
///  a state where all referenced resources are safe to destroy.
pub proof fn lemma_full_frame_loop_safe(
    inv: FrameInvariant,
    resource: ResourceId,
)
    requires
        frame_lifecycle_valid(FrameLifecycleState::Idle, inv),
        inv.frame.submit_info.referenced_resources.contains(resource),
        forall|i: int| 0 <= i < inv.dev.pending_submissions.len()
            ==> !inv.dev.pending_submissions[i].referenced_resources.contains(resource),
        submission_valid(
            inv.frame.submit_info, inv.cb_states, inv.sem_states,
            inv.fence_states, inv.lifecycle_states, inv.queue.queue_id, inv.thread, inv.reg,
        ),
    ensures
        ({
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
    lemma_full_frame_safe(inv, resource);
}

} //  verus!
