use vstd::prelude::*;
use crate::completion::*;
use crate::resource::*;
use crate::command::*;
use crate::lifetime::*;
use crate::fence::*;
use crate::semaphore::*;
use crate::sync::*;
use crate::submit::*;
use crate::device::*;
use super::device::RuntimeDevice;

verus! {

/// Runtime completion tracker: ghost tracking of pending submissions and completion state.
pub struct RuntimeCompletionTracker {
    /// Ghost pending submission records.
    pub pending: Ghost<Seq<SubmissionRecord>>,
}

/// Create an empty completion tracker (no pending submissions).
pub fn create_completion_tracker_exec() -> (out: RuntimeCompletionTracker)
    ensures out.pending@.len() == 0,
{
    RuntimeCompletionTracker {
        pending: Ghost(Seq::empty()),
    }
}

/// Record a submission's semaphore signaling.
/// Ghost-only: updates the tracker's pending list with a new submission record.
pub fn add_submission_exec(
    tracker: &mut RuntimeCompletionTracker,
    record: Ghost<SubmissionRecord>,
)
    ensures tracker.pending@ == old(tracker).pending@.push(record@),
{
    tracker.pending = Ghost(tracker.pending@.push(record@));
}

/// Mark a submission as completed by submission id.
/// Updates the ghost state to reflect GPU completion.
pub fn mark_completed_exec(
    tracker: &mut RuntimeCompletionTracker,
    sub_id: Ghost<nat>,
)
    ensures tracker.pending@ == Seq::new(
        old(tracker).pending@.len() as nat,
        |i: int| if old(tracker).pending@[i].id == sub_id@ {
            SubmissionRecord { completed: true, ..old(tracker).pending@[i] }
        } else {
            old(tracker).pending@[i]
        },
    ),
{
    tracker.pending = Ghost(Seq::new(
        tracker.pending@.len() as nat,
        |i: int| if tracker.pending@[i].id == sub_id@ {
            SubmissionRecord { completed: true, ..tracker.pending@[i] }
        } else {
            tracker.pending@[i]
        },
    ));
}

/// Signal semaphores for a completed submission.
/// Ghost update: applies signal_semaphores_ghost to the provided sem states.
pub fn signal_semaphores_exec(
    sems: Ghost<Seq<nat>>,
    sem_states: Ghost<Map<nat, SemaphoreState>>,
    resource_states: Ghost<Map<ResourceId, SyncState>>,
) -> (out: Ghost<Map<nat, SemaphoreState>>)
    ensures out@ == signal_semaphores_ghost(sems@, sem_states@, resource_states@),
{
    Ghost(signal_semaphores_ghost(sems@, sem_states@, resource_states@))
}

/// Complete a submission: transition CBs, signal semaphores, signal fence.
/// Ghost update: applies complete_submission_ghost.
pub fn complete_submission_exec(
    record: Ghost<SubmissionRecord>,
    cb_states: Ghost<Map<nat, CommandBufferState>>,
    sem_states: Ghost<Map<nat, SemaphoreState>>,
    fence_states: Ghost<Map<nat, FenceState>>,
    resource_states: Ghost<Map<ResourceId, SyncState>>,
) -> (out: Ghost<(Map<nat, CommandBufferState>, Map<nat, SemaphoreState>, Map<nat, FenceState>)>)
    ensures out@ == complete_submission_ghost(record@, cb_states@, sem_states@, fence_states@, resource_states@),
{
    Ghost(complete_submission_ghost(record@, cb_states@, sem_states@, fence_states@, resource_states@))
}

/// Fence wait: mark all submissions with this fence as completed, clean up, reset fence.
/// Ghost update: applies fence_wait_ghost.
pub fn fence_wait_exec(
    dev_state: Ghost<DeviceState>,
    fence_id: Ghost<nat>,
    fence_states: Ghost<Map<nat, FenceState>>,
) -> (out: Ghost<(DeviceState, Map<nat, FenceState>)>)
    requires fence_states@.contains_key(fence_id@),
    ensures out@ == fence_wait_ghost(dev_state@, fence_id@, fence_states@),
{
    Ghost(fence_wait_ghost(dev_state@, fence_id@, fence_states@))
}

// ── Proofs ──────────────────────────────────────────────────────────

/// An empty tracker has no pending submissions.
pub proof fn lemma_empty_tracker_no_pending()
    ensures
        Seq::<SubmissionRecord>::empty().len() == 0,
{
}

/// After adding a submission, the tracker has one more entry.
pub proof fn lemma_add_submission_increases_count(
    tracker: RuntimeCompletionTracker,
    record: SubmissionRecord,
)
    ensures
        tracker.pending@.push(record).len() == tracker.pending@.len() + 1,
{
}

} // verus!
