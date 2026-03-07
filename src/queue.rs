use vstd::prelude::*;
use crate::resource::*;
use crate::command::*;
use crate::lifetime::*;
use crate::fence::*;
use crate::semaphore::*;

verus! {

/// Ghost state for a Vulkan queue.
pub struct QueueState {
    /// Unique queue identifier.
    pub queue_id: nat,
    /// Monotonically increasing submission sequence number.
    pub next_sequence: nat,
}

/// Describes a single vkQueueSubmit call.
pub struct SubmitInfo {
    /// Semaphore ids to wait on before execution begins.
    pub wait_semaphores: Seq<nat>,
    /// Command buffer ids to execute, in order.
    pub command_buffers: Seq<nat>,
    /// Semaphore ids to signal when execution completes.
    pub signal_semaphores: Seq<nat>,
    /// Optional fence to signal on completion.
    pub fence_id: Option<nat>,
    /// Ghost set of all resources referenced by the command buffers.
    pub referenced_resources: Set<ResourceId>,
}

/// A queue is well-formed (placeholder for future constraints).
pub open spec fn queue_well_formed(q: QueueState) -> bool {
    true
}

/// A submit info is well-formed if it has at least one command buffer.
pub open spec fn submit_info_well_formed(info: SubmitInfo) -> bool {
    info.command_buffers.len() > 0
}

/// All command buffers referenced by the submission are in the map and Executable.
pub open spec fn all_command_buffers_executable(
    info: SubmitInfo,
    cb_states: Map<nat, CommandBufferState>,
) -> bool {
    forall|i: int| #![trigger info.command_buffers[i]]
        0 <= i < info.command_buffers.len()
        ==> cb_states.contains_key(info.command_buffers[i])
            && cb_states[info.command_buffers[i]] == CommandBufferState::Executable
}

/// All wait semaphores are in the map and currently signaled.
pub open spec fn all_wait_semaphores_signaled(
    info: SubmitInfo,
    sem_states: Map<nat, SemaphoreState>,
) -> bool {
    forall|i: int| #![trigger info.wait_semaphores[i]]
        0 <= i < info.wait_semaphores.len()
        ==> sem_states.contains_key(info.wait_semaphores[i])
            && sem_states[info.wait_semaphores[i]].signaled
}

/// If a fence is specified, it must be alive and unsignaled.
pub open spec fn fence_available_for_submit(
    info: SubmitInfo,
    fence_states: Map<nat, FenceState>,
) -> bool {
    match info.fence_id {
        None => true,
        Some(fid) => {
            fence_states.contains_key(fid)
            && fence_well_formed(fence_states[fid])
            && !fence_states[fid].signaled
        },
    }
}

/// A submission is valid if all preconditions are met.
pub open spec fn submission_valid(
    info: SubmitInfo,
    cb_states: Map<nat, CommandBufferState>,
    sem_states: Map<nat, SemaphoreState>,
    fence_states: Map<nat, FenceState>,
) -> bool {
    submit_info_well_formed(info)
    && all_command_buffers_executable(info, cb_states)
    && all_wait_semaphores_signaled(info, sem_states)
    && fence_available_for_submit(info, fence_states)
}

/// Ghost submit: advance the queue sequence and produce a submission record.
/// Returns (updated queue, new submission record).
pub open spec fn submit_ghost(
    queue: QueueState,
    info: SubmitInfo,
) -> (QueueState, SubmissionRecord) {
    let record = SubmissionRecord {
        id: queue.next_sequence,
        referenced_resources: info.referenced_resources,
        fence_id: info.fence_id,
        completed: false,
        command_buffers: info.command_buffers,
        signal_semaphores: info.signal_semaphores,
    };
    let new_queue = QueueState {
        next_sequence: queue.next_sequence + 1,
        ..queue
    };
    (new_queue, record)
}

// ── Lemmas ──────────────────────────────────────────────────────────────

/// Submitting increments the queue's next_sequence by 1.
pub proof fn lemma_submit_increments_sequence(queue: QueueState, info: SubmitInfo)
    ensures submit_ghost(queue, info).0.next_sequence == queue.next_sequence + 1,
{
}

/// The submission record returned by submit_ghost is not completed
/// and carries the correct fence_id and referenced resources.
pub proof fn lemma_submit_creates_pending_record(queue: QueueState, info: SubmitInfo)
    ensures ({
        let record = submit_ghost(queue, info).1;
        !record.completed
        && record.fence_id == info.fence_id
        && record.referenced_resources == info.referenced_resources
        && record.command_buffers == info.command_buffers
        && record.signal_semaphores == info.signal_semaphores
    }),
{
}

/// A valid submission implies all command buffers are Executable.
pub proof fn lemma_valid_submission_has_executable_buffers(
    info: SubmitInfo,
    cb_states: Map<nat, CommandBufferState>,
    sem_states: Map<nat, SemaphoreState>,
    fence_states: Map<nat, FenceState>,
)
    requires submission_valid(info, cb_states, sem_states, fence_states),
    ensures all_command_buffers_executable(info, cb_states),
{
}

/// The submission record's fence_id matches the input fence_id.
pub proof fn lemma_submit_record_matches_fence(
    queue: QueueState,
    info: SubmitInfo,
    fence_id: Option<nat>,
)
    requires info.fence_id == fence_id,
    ensures submit_ghost(queue, info).1.fence_id == fence_id,
{
}

} // verus!
