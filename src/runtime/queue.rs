use vstd::prelude::*;
use crate::device::*;
use crate::lifetime::*;
use super::device::*;

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

/// Exec: submit a command buffer to the queue (ghost-level updates device).
pub fn submit_exec(
    dev: &mut RuntimeDevice,
    queue: &RuntimeQueue,
    submission: Ghost<SubmissionRecord>,
)
    requires
        runtime_device_wf(&*old(dev)),
        submission@.queue_id == queue@,
    ensures
        dev@.pending_submissions == old(dev)@.pending_submissions.push(submission@),
        dev@.live_buffers == old(dev)@.live_buffers,
        dev@.live_images == old(dev)@.live_images,
{
    let ghost new_state = DeviceState {
        pending_submissions: dev.state@.pending_submissions.push(submission@),
        ..dev.state@
    };
    dev.state = Ghost(new_state);
}

/// Exec: queue wait idle — removes all submissions for this queue.
pub fn queue_wait_idle_exec(
    dev: &mut RuntimeDevice,
    queue: &RuntimeQueue,
)
    requires
        runtime_device_wf(&*old(dev)),
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
    queue: &RuntimeQueue,
    submission: Ghost<SubmissionRecord>,
)
    requires
        runtime_device_wf(dev),
        submission@.queue_id == queue@,
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
