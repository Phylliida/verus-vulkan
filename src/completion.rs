use vstd::prelude::*;
use crate::resource::*;
use crate::command::*;
use crate::lifetime::*;
use crate::fence::*;
use crate::semaphore::*;
use crate::sync::*;
use crate::submit::*;
use crate::device::*;

verus! {

// ── Spec Functions ──────────────────────────────────────────────────────

/// Recursively transition each command buffer in `cbs` from Pending to Executable.
pub open spec fn transition_cbs_to_executable(
    cbs: Seq<nat>,
    cb_states: Map<nat, CommandBufferState>,
) -> Map<nat, CommandBufferState>
    decreases cbs.len(),
{
    if cbs.len() == 0 {
        cb_states
    } else {
        let prefix_result = transition_cbs_to_executable(
            cbs.subrange(0, cbs.len() - 1),
            cb_states,
        );
        prefix_result.insert(cbs.last(), CommandBufferState::Executable)
    }
}

/// Recursively signal each semaphore in `sems`, depositing the given resource states.
pub open spec fn signal_semaphores_ghost(
    sems: Seq<nat>,
    sem_states: Map<nat, SemaphoreState>,
    resource_states: Map<ResourceId, SyncState>,
) -> Map<nat, SemaphoreState>
    decreases sems.len(),
{
    if sems.len() == 0 {
        sem_states
    } else {
        let prefix_result = signal_semaphores_ghost(
            sems.subrange(0, sems.len() - 1),
            sem_states,
            resource_states,
        );
        let old_sem = prefix_result[sems.last()];
        prefix_result.insert(sems.last(), signal_semaphore_ghost(old_sem, resource_states))
    }
}

/// Complete a submission: transition CBs to Executable, signal semaphores, signal fence.
pub open spec fn complete_submission_ghost(
    record: SubmissionRecord,
    cb_states: Map<nat, CommandBufferState>,
    sem_states: Map<nat, SemaphoreState>,
    fence_states: Map<nat, FenceState>,
    resource_states: Map<ResourceId, SyncState>,
) -> (Map<nat, CommandBufferState>, Map<nat, SemaphoreState>, Map<nat, FenceState>) {
    let new_cbs = transition_cbs_to_executable(record.command_buffers, cb_states);
    let new_sems = signal_semaphores_ghost(record.signal_semaphores, sem_states, resource_states);
    let new_fences = match record.fence_id {
        Some(fid) => fence_states.insert(fid, signal_fence_ghost(fence_states[fid], record.id)),
        None => fence_states,
    };
    (new_cbs, new_sems, new_fences)
}

/// Mark a specific submission as completed in the device's pending submissions.
pub open spec fn mark_submission_completed(
    dev: DeviceState,
    sub_id: nat,
) -> DeviceState {
    DeviceState {
        pending_submissions: Seq::new(
            dev.pending_submissions.len(),
            |i: int| if dev.pending_submissions[i].id == sub_id {
                SubmissionRecord { completed: true, ..dev.pending_submissions[i] }
            } else {
                dev.pending_submissions[i]
            },
        ),
        ..dev
    }
}

/// Host-side fence wait: mark all submissions with this fence as completed,
/// remove completed, and reset the fence.
pub open spec fn fence_wait_ghost(
    dev: DeviceState,
    fence_id: nat,
    fence_states: Map<nat, FenceState>,
) -> (DeviceState, Map<nat, FenceState>) {
    let marked = mark_fence_completed(dev.pending_submissions, fence_id);
    let cleaned = remove_completed(marked);
    let new_dev = DeviceState {
        pending_submissions: cleaned,
        ..dev
    };
    let new_fences = fence_states.insert(fence_id, reset_fence_ghost(fence_states[fence_id]));
    (new_dev, new_fences)
}

/// True iff a resource can be safely destroyed: no pending submissions reference it.
pub open spec fn safe_to_destroy_resource(
    dev: DeviceState,
    resource: ResourceId,
) -> bool {
    no_pending_references(dev.pending_submissions, resource)
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// After completion, all command buffers in the record are Executable.
pub proof fn lemma_complete_restores_executable(
    record: SubmissionRecord,
    cb_states: Map<nat, CommandBufferState>,
    i: int,
)
    requires
        0 <= i < record.command_buffers.len(),
        forall|j: int| 0 <= j < record.command_buffers.len()
            ==> cb_states.contains_key(#[trigger] record.command_buffers[j]),
    ensures ({
        let result = transition_cbs_to_executable(record.command_buffers, cb_states);
        result.contains_key(record.command_buffers[i])
        && result[record.command_buffers[i]] == CommandBufferState::Executable
    }),
    decreases record.command_buffers.len(),
{
    let cbs = record.command_buffers;
    // Mirror the structure of lemma_transition_sets_pending
    if cbs.len() > 0 {
        let prefix = cbs.subrange(0, cbs.len() - 1);

        assert forall|j: int| 0 <= j < prefix.len()
            implies cb_states.contains_key(#[trigger] prefix[j]) by {
            assert(prefix[j] == cbs[j]);
        }

        if i == cbs.len() - 1 {
            // Last element, inserted directly
        } else {
            assert(cbs[i] == prefix[i]);
            let prefix_record = SubmissionRecord { command_buffers: prefix, ..record };
            lemma_complete_restores_executable(prefix_record, cb_states, i);
        }
    }
}

/// After completion, if a fence was specified, it becomes signaled.
pub proof fn lemma_complete_signals_fence(
    record: SubmissionRecord,
    cb_states: Map<nat, CommandBufferState>,
    sem_states: Map<nat, SemaphoreState>,
    fence_states: Map<nat, FenceState>,
    resource_states: Map<ResourceId, SyncState>,
)
    requires
        record.fence_id.is_some(),
        fence_states.contains_key(record.fence_id.unwrap()),
    ensures ({
        let (_, _, new_fences) = complete_submission_ghost(
            record, cb_states, sem_states, fence_states, resource_states,
        );
        new_fences[record.fence_id.unwrap()].signaled
    }),
{
}

/// After completion, all signal semaphores become signaled.
pub proof fn lemma_complete_signals_semaphores(
    record: SubmissionRecord,
    sem_states: Map<nat, SemaphoreState>,
    resource_states: Map<ResourceId, SyncState>,
    i: int,
)
    requires
        0 <= i < record.signal_semaphores.len(),
        forall|j: int| 0 <= j < record.signal_semaphores.len()
            ==> sem_states.contains_key(#[trigger] record.signal_semaphores[j]),
    ensures ({
        let result = signal_semaphores_ghost(record.signal_semaphores, sem_states, resource_states);
        result.contains_key(record.signal_semaphores[i])
        && result[record.signal_semaphores[i]].signaled
    }),
    decreases record.signal_semaphores.len(),
{
    let sems = record.signal_semaphores;

    if sems.len() > 0 {
        let prefix = sems.subrange(0, sems.len() - 1);

        assert forall|j: int| 0 <= j < prefix.len()
            implies sem_states.contains_key(#[trigger] prefix[j]) by {
            assert(prefix[j] == sems[j]);
        }

        if i == sems.len() - 1 {
            // Last element — signaled by this step
            let prefix_result = signal_semaphores_ghost(prefix, sem_states, resource_states);
            // Need prefix_result.contains_key(sems.last())
            if seq_contains_nat(prefix, sems.last()) {
                lemma_signal_contains_key(prefix, sem_states, resource_states, sems.last());
            } else {
                lemma_signal_preserves_others(prefix, sem_states, resource_states, sems.last());
            }
        } else {
            assert(sems[i] == prefix[i]);
            let prefix_record = SubmissionRecord { signal_semaphores: prefix, ..record };
            lemma_complete_signals_semaphores(prefix_record, sem_states, resource_states, i);

            if sems.last() == sems[i] {
                // Overwritten — still signaled
            } else {
                // Different key, preserved
            }
        }
    }
}

/// Helper: after signal_semaphores_ghost, any key in the seq is in the result.
proof fn lemma_signal_contains_key(
    sems: Seq<nat>,
    sem_states: Map<nat, SemaphoreState>,
    resource_states: Map<ResourceId, SyncState>,
    k: nat,
)
    requires
        seq_contains_nat(sems, k),
        forall|j: int| 0 <= j < sems.len()
            ==> sem_states.contains_key(#[trigger] sems[j]),
    ensures
        signal_semaphores_ghost(sems, sem_states, resource_states).contains_key(k),
    decreases sems.len(),
{
    if sems.len() > 0 {
        let prefix = sems.subrange(0, sems.len() - 1);

        assert forall|j: int| 0 <= j < prefix.len()
            implies sem_states.contains_key(#[trigger] prefix[j]) by {
            assert(prefix[j] == sems[j]);
        }

        if sems.last() == k {
            let prefix_result = signal_semaphores_ghost(prefix, sem_states, resource_states);
            if seq_contains_nat(prefix, k) {
                lemma_signal_contains_key(prefix, sem_states, resource_states, k);
            } else {
                lemma_signal_preserves_others(prefix, sem_states, resource_states, k);
            }
        } else {
            lemma_signal_contains_key(prefix, sem_states, resource_states, k);
        }
    }
}

/// signal_semaphores_ghost preserves entries not in the sequence.
proof fn lemma_signal_preserves_others(
    sems: Seq<nat>,
    sem_states: Map<nat, SemaphoreState>,
    resource_states: Map<ResourceId, SyncState>,
    k: nat,
)
    requires
        !seq_contains_nat(sems, k),
        sem_states.contains_key(k),
    ensures
        signal_semaphores_ghost(sems, sem_states, resource_states).contains_key(k)
        && signal_semaphores_ghost(sems, sem_states, resource_states)[k] == sem_states[k],
    decreases sems.len(),
{
    if sems.len() > 0 {
        let prefix = sems.subrange(0, sems.len() - 1);
        lemma_signal_preserves_others(prefix, sem_states, resource_states, k);
    }
}

/// After a fence wait, if all submissions referencing the resource had this fence_id,
/// the resource is safe to destroy.
pub proof fn lemma_fence_wait_enables_destroy(
    dev: DeviceState,
    fence_id: nat,
    fence_states: Map<nat, FenceState>,
    resource: ResourceId,
)
    requires
        fence_states.contains_key(fence_id),
        // Every submission referencing this resource has this fence_id
        forall|i: int| 0 <= i < dev.pending_submissions.len()
            && dev.pending_submissions[i].referenced_resources.contains(resource)
            ==> dev.pending_submissions[i].fence_id == Some(fence_id),
    ensures ({
        let (new_dev, _) = fence_wait_ghost(dev, fence_id, fence_states);
        safe_to_destroy_resource(new_dev, resource)
    }),
{
    // Delegate to the existing lemma in lifetime.rs
    lemma_wait_clears_fence_submissions(dev.pending_submissions, fence_id, resource);
}

} // verus!
