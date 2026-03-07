use vstd::prelude::*;
use crate::resource::*;
use crate::command::*;
use crate::lifetime::*;
use crate::fence::*;
use crate::semaphore::*;
use crate::sync_token::*;

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

/// A submission is valid if all preconditions are met, including
/// thread safety: the submitting thread must hold exclusive access
/// to the queue, and all submitted CBs must not be held by others.
///
/// Per Vulkan spec: "queue is an externally synchronized parameter"
/// for vkQueueSubmit.
pub open spec fn submission_valid(
    info: SubmitInfo,
    cb_states: Map<nat, CommandBufferState>,
    sem_states: Map<nat, SemaphoreState>,
    fence_states: Map<nat, FenceState>,
    queue_id: nat,
    thread: ThreadId,
    reg: TokenRegistry,
) -> bool {
    submit_info_well_formed(info)
    && all_command_buffers_executable(info, cb_states)
    && all_wait_semaphores_signaled(info, sem_states)
    && fence_available_for_submit(info, fence_states)
    // Thread safety: exclusive queue access
    && holds_exclusive(reg, queue_id, thread)
    // Thread safety: fence access (if specified)
    && (info.fence_id.is_none()
        || holds_exclusive(reg, info.fence_id.unwrap(), thread))
    // Thread safety: no other thread exclusively holds submitted CBs
    && (forall|i: int| #![trigger info.command_buffers[i]]
        0 <= i < info.command_buffers.len() ==>
        not_held_by_other(reg, info.command_buffers[i], thread))
}

/// Ghost submit: advance the queue sequence and produce a submission record.
/// Returns (updated queue, new submission record).
///
/// Requires exclusive queue access.
pub open spec fn submit_ghost(
    queue: QueueState,
    info: SubmitInfo,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<(QueueState, SubmissionRecord)> {
    if !holds_exclusive(reg, queue.queue_id, thread) {
        None
    } else {
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
        Some((new_queue, record))
    }
}

// ── Lemmas ──────────────────────────────────────────────────────────────

/// Submitting increments the queue's next_sequence by 1.
pub proof fn lemma_submit_increments_sequence(
    queue: QueueState,
    info: SubmitInfo,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires holds_exclusive(reg, queue.queue_id, thread),
    ensures
        submit_ghost(queue, info, thread, reg).is_some(),
        submit_ghost(queue, info, thread, reg).unwrap().0.next_sequence
            == queue.next_sequence + 1,
{
}

/// The submission record returned by submit_ghost is not completed
/// and carries the correct fence_id and referenced resources.
pub proof fn lemma_submit_creates_pending_record(
    queue: QueueState,
    info: SubmitInfo,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires holds_exclusive(reg, queue.queue_id, thread),
    ensures ({
        let record = submit_ghost(queue, info, thread, reg).unwrap().1;
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
    queue_id: nat,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires submission_valid(info, cb_states, sem_states, fence_states, queue_id, thread, reg),
    ensures all_command_buffers_executable(info, cb_states),
{
}

/// The submission record's fence_id matches the input fence_id.
pub proof fn lemma_submit_record_matches_fence(
    queue: QueueState,
    info: SubmitInfo,
    fence_id: Option<nat>,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires
        info.fence_id == fence_id,
        holds_exclusive(reg, queue.queue_id, thread),
    ensures
        submit_ghost(queue, info, thread, reg).unwrap().1.fence_id == fence_id,
{
}

/// Without exclusive queue access, submit_ghost returns None.
pub proof fn lemma_no_queue_access_no_submit(
    queue: QueueState,
    info: SubmitInfo,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires !holds_exclusive(reg, queue.queue_id, thread),
    ensures submit_ghost(queue, info, thread, reg).is_none(),
{
}

/// A valid submission guarantees the submitter holds the queue.
pub proof fn lemma_valid_submission_holds_queue(
    info: SubmitInfo,
    cb_states: Map<nat, CommandBufferState>,
    sem_states: Map<nat, SemaphoreState>,
    fence_states: Map<nat, FenceState>,
    queue_id: nat,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires submission_valid(info, cb_states, sem_states, fence_states, queue_id, thread, reg),
    ensures holds_exclusive(reg, queue_id, thread),
{
}

} // verus!
