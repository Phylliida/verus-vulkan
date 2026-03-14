use vstd::prelude::*;
use crate::device::*;
use crate::fence::*;
use crate::lifetime::*;
use crate::resource::*;
use crate::memory_aliasing::*;
use crate::queue::*;
use crate::semaphore::*;
use crate::sync_token::*;
use super::device::*;
use super::command_buffer::CommandBufferStatus;
use super::memory_aliasing::*;

verus! {

/// Runtime wrapper for a Vulkan queue.
pub struct RuntimeQueue {
    /// Opaque handle (maps to VkQueue).
    pub handle: u64,
    /// Queue family index.
    pub family_index: u32,
    /// Queue index within the family.
    pub queue_index: u32,
    /// Ghost queue ID for tracking.
    pub queue_id: Ghost<nat>,
}

impl View for RuntimeQueue {
    type V = nat;
    open spec fn view(&self) -> nat { self.queue_id@ }
}

/// Exec: submit command buffers to the queue (ghost-level updates device).
/// Caller must prove all referenced command buffers are Executable via a status map
/// keyed by CB id. Also marks referenced resources as in-flight in the aliasing tracker.
pub fn submit_exec(
    dev: &mut RuntimeDevice,
    queue: &RuntimeQueue,
    submission: Ghost<SubmissionRecord>,
    submit_info: Ghost<SubmitInfo>,
    cb_views: Ghost<Seq<CommandBufferStatus>>,
    wait_sem_views: Ghost<Seq<SemaphoreState>>,
    signal_sem_views: Ghost<Seq<SemaphoreState>>,
    fence_view: Ghost<Option<FenceState>>,
    aliasing_tracker: &mut RuntimeAliasingTracker,
    thread: Ghost<ThreadId>,
    reg: Ghost<TokenRegistry>,
)
    requires
        runtime_device_wf(&*old(dev)),
        submission@.queue_id == queue@,
        submission@.command_buffers.len() > 0,
        // Thread safety: exclusive queue access
        holds_exclusive(reg@, SyncObjectId::Queue(queue@), thread@),
        // Thread safety: CBs not held by other threads
        forall|i: int| 0 <= i < submission@.command_buffers.len()
            ==> not_held_by_other(reg@, SyncObjectId::Handle(#[trigger] submission@.command_buffers[i]), thread@),
        // CB views: parallel sequence, all must be Executable
        cb_views@.len() == submission@.command_buffers.len(),
        forall|i: int| 0 <= i < cb_views@.len()
            ==> #[trigger] cb_views@[i] == CommandBufferStatus::Executable,
        // Wait semaphores must be signaled (parallel sequence)
        wait_sem_views@.len() == submit_info@.wait_semaphores.len(),
        forall|i: int| 0 <= i < wait_sem_views@.len()
            ==> (#[trigger] wait_sem_views@[i]).id == submit_info@.wait_semaphores[i]
                && wait_sem_views@[i].signaled,
        // Signal semaphores must be unsignaled (parallel sequence)
        signal_sem_views@.len() == submit_info@.signal_semaphores.len(),
        forall|i: int| 0 <= i < signal_sem_views@.len()
            ==> (#[trigger] signal_sem_views@[i]).id == submit_info@.signal_semaphores[i]
                && !signal_sem_views@[i].signaled,
        // Fence (if any) must be unsignaled and not pending
        fence_view@.is_some() == submit_info@.fence_id.is_some(),
        fence_view@.is_some() ==> (
            fence_view@.unwrap().id == submit_info@.fence_id.unwrap()
            && !fence_view@.unwrap().signaled
            && fence_not_pending(submit_info@.fence_id.unwrap(), old(dev)@.pending_submissions)
        ),
        // Submission record must be consistent with the submit info
        submission@.command_buffers =~= submit_info@.command_buffers,
        submission@.signal_semaphores =~= submit_info@.signal_semaphores,
        submission@.fence_id == submit_info@.fence_id,
        submission@.referenced_resources =~= submit_info@.referenced_resources,
        !submission@.completed,
        // All referenced resources are bound in the aliasing tracker
        forall|r: ResourceId| submission@.referenced_resources.contains(r)
            ==> old(aliasing_tracker).bindings@.contains_key(r),
        // No aliasing hazard: combined in-flight set has no overlapping pairs
        no_in_flight_overlaps(old(aliasing_tracker)),
        forall|r1: ResourceId, r2: ResourceId|
            (old(aliasing_tracker).in_flight@.contains(r1) || submission@.referenced_resources.contains(r1))
            && (old(aliasing_tracker).in_flight@.contains(r2) || submission@.referenced_resources.contains(r2))
            && r1 != r2
            && old(aliasing_tracker).bindings@.contains_key(r1)
            && old(aliasing_tracker).bindings@.contains_key(r2)
            ==> !ranges_overlap(
                old(aliasing_tracker).bindings@[r1],
                old(aliasing_tracker).bindings@[r2],
            ),
    ensures
        dev@.pending_submissions == old(dev)@.pending_submissions.push(submission@),
        dev@.live_buffers == old(dev)@.live_buffers,
        dev@.live_images == old(dev)@.live_images,
        aliasing_tracker.in_flight@ == old(aliasing_tracker).in_flight@.union(submission@.referenced_resources),
        aliasing_tracker.bindings@ == old(aliasing_tracker).bindings@,
{
    let ghost new_state = DeviceState {
        pending_submissions: dev.state@.pending_submissions.push(submission@),
        ..dev.state@
    };
    dev.state = Ghost(new_state);
    aliasing_tracker.in_flight = Ghost(aliasing_tracker.in_flight@.union(submission@.referenced_resources));
}

/// Exec: queue wait idle — removes all submissions for this queue.
/// Caller must prove exclusive access to the queue.
pub fn queue_wait_idle_exec(
    dev: &mut RuntimeDevice,
    queue: &RuntimeQueue,
    thread: Ghost<ThreadId>,
    reg: Ghost<TokenRegistry>,
)
    requires
        runtime_device_wf(&*old(dev)),
        holds_exclusive(reg@, SyncObjectId::Queue(queue@), thread@),
    ensures
        dev@ == queue_wait_idle_ghost(old(dev)@, queue@),
{
    dev.state = Ghost(queue_wait_idle_ghost(dev.state@, queue@));
}

// ── Extended Specs & Proofs ──────────────────────────────────────────

/// Queue ID.
pub open spec fn queue_id(queue: &RuntimeQueue) -> nat {
    queue@
}

/// Proof: submit adds exactly one submission.
pub proof fn lemma_submit_adds_one(
    dev: &RuntimeDevice,
    submission: Ghost<SubmissionRecord>,
)
    requires
        runtime_device_wf(dev),
    ensures ({
        let new_state = DeviceState {
            pending_submissions: dev@.pending_submissions.push(submission@),
            ..dev@
        };
        new_state.pending_submissions.len() == dev@.pending_submissions.len() + 1
    }),
{
}

/// Proof: queue wait idle preserves well-formedness.
pub proof fn lemma_queue_wait_idle_wf(
    dev: &RuntimeDevice,
    queue: &RuntimeQueue,
)
    requires runtime_device_wf(dev),
    ensures device_well_formed(queue_wait_idle_ghost(dev@, queue@)),
{
    lemma_queue_wait_idle_preserves_well_formed(dev@, queue@);
}

} // verus!
