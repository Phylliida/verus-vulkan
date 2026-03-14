use vstd::prelude::*;
use crate::resource::*;
use crate::command::*;
use crate::lifetime::*;
use crate::device::*;
use crate::fence::*;
use crate::semaphore::*;
use crate::queue::*;
use crate::submit::*;
use crate::completion::*;
use crate::recording_commands::*;
use crate::recording::*;
use crate::sync::*;
use crate::sync_token::*;

verus! {

// ── End-to-End Safety Proofs ────────────────────────────────────────────
//
// These proofs demonstrate that the Vulkan ghost state model correctly
// tracks resource lifetimes through the full create→record→submit→wait→destroy
// lifecycle.
//
// Every submission proof now requires the submitting thread to hold
// exclusive access to the queue — enforcing thread safety at the proof level.

/// **Crown jewel**: A resource that is only used in one submission, protected
/// by a fence, can be safely destroyed after waiting on that fence.
///
/// This is the fundamental safety property of the Vulkan memory model:
/// GPU work references resources, fences signal when work completes,
/// and after a fence wait the host can safely destroy those resources.
///
/// The caller must prove they hold exclusive queue access (thread safety).
pub proof fn lemma_submit_wait_destroy_safe(
    dev: DeviceState,
    queue: QueueState,
    info: SubmitInfo,
    fence_id: nat,
    resource: ResourceId,
    fence_states: Map<nat, FenceState>,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires
        // Thread safety: submitter holds the queue
        holds_exclusive(reg, SyncObjectId::Queue(queue.queue_id), thread),
        // The submission uses a fence
        info.fence_id == Some(fence_id),
        fence_states.contains_key(fence_id),
        // The resource is referenced by this submission
        info.referenced_resources.contains(resource),
        // No prior submission references this resource at all
        forall|i: int| 0 <= i < dev.pending_submissions.len()
            ==> !dev.pending_submissions[i].referenced_resources.contains(resource),
    ensures ({
        // After submit: resource is in a pending submission
        let (new_queue, record) = submit_ghost(queue, info, thread, reg).unwrap();
        let new_dev = DeviceState {
            pending_submissions: dev.pending_submissions.push(record),
            ..dev
        };
        // After fence wait: resource is safe to destroy
        let (post_wait_dev, _) = fence_wait_ghost(new_dev, fence_id, fence_states);
        safe_to_destroy_resource(post_wait_dev, resource)
    }),
{
    let (new_queue, record) = submit_ghost(queue, info, thread, reg).unwrap();
    let new_subs = dev.pending_submissions.push(record);
    let new_dev = DeviceState {
        pending_submissions: new_subs,
        ..dev
    };

    // Establish: every submission in new_subs referencing resource has this fence_id
    assert forall|i: int| 0 <= i < new_subs.len()
        && new_subs[i].referenced_resources.contains(resource)
        implies new_subs[i].fence_id == Some(fence_id) by {
        if i < dev.pending_submissions.len() as int {
            // Old submission: doesn't reference resource at all
            assert(new_subs[i] == dev.pending_submissions[i]);
        } else {
            // New submission: record.fence_id == Some(fence_id)
            assert(new_subs[i] == record);
        }
    }

    lemma_fence_wait_enables_destroy(new_dev, fence_id, fence_states, resource);
}

/// Simplified version: a fresh resource (not in any prior submission)
/// submitted with a fence can be destroyed after fence wait.
pub proof fn lemma_fresh_resource_submit_wait_destroy(
    queue: QueueState,
    info: SubmitInfo,
    fence_id: nat,
    resource: ResourceId,
    fence_states: Map<nat, FenceState>,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires
        holds_exclusive(reg, SyncObjectId::Queue(queue.queue_id), thread),
        info.fence_id == Some(fence_id),
        fence_states.contains_key(fence_id),
        info.referenced_resources.contains(resource),
    ensures ({
        // Start with empty submissions
        let dev = DeviceState {
            pending_submissions: Seq::<SubmissionRecord>::empty(),
            heap_usage: Map::empty(),
            heap_capacity: Map::empty(),
            num_heaps: 0,
            memory_type_to_heap: Map::empty(),
            num_memory_types: 0,
            live_buffers: 0,
            live_images: 0,
            live_pipelines: 0,
            live_descriptor_pools: 0,
            limits: DeviceLimits {
                min_uniform_buffer_offset_alignment: 1,
                min_storage_buffer_offset_alignment: 1,
                min_texel_buffer_offset_alignment: 1,
                max_push_constants_size: 0,
            },
            format_properties: Map::empty(),
            lifecycle_registry: Map::empty(),
        };
        let (_, record) = submit_ghost(queue, info, thread, reg).unwrap();
        let new_dev = DeviceState {
            pending_submissions: dev.pending_submissions.push(record),
            ..dev
        };
        let (post_wait_dev, _) = fence_wait_ghost(new_dev, fence_id, fence_states);
        safe_to_destroy_resource(post_wait_dev, resource)
    }),
{
    let dev = DeviceState {
        pending_submissions: Seq::<SubmissionRecord>::empty(),
        heap_usage: Map::empty(),
        heap_capacity: Map::empty(),
        num_heaps: 0,
        memory_type_to_heap: Map::empty(),
        num_memory_types: 0,
        live_buffers: 0,
        live_images: 0,
        live_pipelines: 0,
        live_descriptor_pools: 0,
        limits: DeviceLimits {
            min_uniform_buffer_offset_alignment: 1,
            min_storage_buffer_offset_alignment: 1,
            min_texel_buffer_offset_alignment: 1,
            max_push_constants_size: 0,
        },
        format_properties: Map::empty(),
        lifecycle_registry: Map::empty(),
    };

    // Empty submissions → no submission references resource
    lemma_submit_wait_destroy_safe(dev, queue, info, fence_id, resource, fence_states, thread, reg);
}

/// The command buffer lifecycle is correctly maintained through submit→complete.
pub proof fn lemma_cb_lifecycle_through_frame(
    cb_id: nat,
    cb_states: Map<nat, CommandBufferState>,
)
    requires
        cb_states.contains_key(cb_id),
        cb_states[cb_id] == CommandBufferState::Executable,
    ensures ({
        // Submit: Executable → Pending
        let cbs = seq![cb_id];
        let after_submit = transition_cbs_to_pending(cbs, cb_states);
        // Complete: Pending → Executable
        let after_complete = transition_cbs_to_executable(cbs, after_submit);
        after_complete.contains_key(cb_id)
        && after_complete[cb_id] == CommandBufferState::Executable
    }),
{
    let cbs = seq![cb_id];

    // Submit transitions cb_id to Pending
    lemma_transition_sets_pending(cbs, cb_states, 0);
    let after_submit = transition_cbs_to_pending(cbs, cb_states);

    // The record for complete needs cbs in the map
    assert(after_submit.contains_key(cb_id));

    // Complete transitions cb_id back to Executable
    let record = SubmissionRecord {
        id: 0,
        queue_id: 0,
        referenced_resources: Set::empty(),
        fence_id: None,
        completed: false,
        command_buffers: cbs,
        signal_semaphores: Seq::empty(),
    };
    lemma_complete_restores_executable(record, after_submit, 0);
}

/// Semaphore lifecycle: signal→wait→signal roundtrip.
pub proof fn lemma_semaphore_signal_wait_cycle(
    sem_id: nat,
    sem_states: Map<nat, SemaphoreState>,
    resource_states: Map<ResourceId, SyncState>,
)
    requires
        sem_states.contains_key(sem_id),
    ensures ({
        // Signal
        let after_signal = signal_semaphores_ghost(
            seq![sem_id], sem_states, resource_states,
        );
        // Wait
        let after_wait = consume_wait_semaphores(
            seq![sem_id], after_signal,
        );
        after_wait.contains_key(sem_id)
        && !after_wait[sem_id].signaled
    }),
{
    let sems = seq![sem_id];

    // After signaling, sem_id is signaled
    let record = SubmissionRecord {
        id: 0,
        queue_id: 0,
        referenced_resources: Set::empty(),
        fence_id: None,
        completed: false,
        command_buffers: Seq::empty(),
        signal_semaphores: sems,
    };
    lemma_complete_signals_semaphores(record, sem_states, resource_states, 0);
    let after_signal = signal_semaphores_ghost(sems, sem_states, resource_states);

    // Establish after_signal.contains_key for consume precondition
    assert(after_signal.contains_key(sem_id));

    // After waiting, sem_id is unsignaled
    lemma_consume_unsignals_waits(sems, after_signal, 0);
}

/// Recording then submitting correctly references all resources.
pub proof fn lemma_recording_references_tracked(
    ctx: RecordingContext,
    resources: Set<ResourceId>,
    resource: ResourceId,
)
    requires resources.contains(resource),
    ensures
        record_draw(ctx, resources).referenced_resources.contains(resource),
{
    lemma_record_accumulates_resources(ctx, resources);
}

} // verus!
