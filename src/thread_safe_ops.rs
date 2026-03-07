use vstd::prelude::*;
use crate::sync_token::*;
use crate::pool_ownership::*;
use crate::command::*;
use crate::command_pool::*;
use crate::queue::*;
use crate::descriptor::*;
use crate::descriptor_update::*;
use crate::resource::*;
use crate::fence::*;
use crate::semaphore::*;
use crate::lifetime::*;
use crate::queue_ownership::*;

verus! {

// ═══════════════════════════════════════════════════════════════════════
// Thread-Safe Operation Wrappers
//
// Each wrapper combines the base operation's spec with the Vulkan spec's
// external synchronization requirements. Using these instead of the
// raw specs forces the caller to prove thread safety.
//
// Per the Vulkan spec §3.6 "Threading Behavior":
// - vkBeginCommandBuffer: externally sync CB + parent pool
// - vkEndCommandBuffer: externally sync CB + parent pool
// - vkQueueSubmit: externally sync queue + fence
// - vkResetCommandPool: externally sync pool
// - vkUpdateDescriptorSets: externally sync dstSet of each write
// - vkAllocateCommandBuffers: externally sync pool
// - vkFreeCommandBuffers: externally sync pool
// - Queue family ownership transfers: externally sync queue
// ═══════════════════════════════════════════════════════════════════════

// ── Command Buffer Recording ────────────────────────────────────────────

/// Thread-safe vkBeginCommandBuffer: requires exclusive access to both
/// the command buffer AND its parent pool (implicit external sync).
///
/// Note: begin_recording already requires exclusive CB access.
/// This additionally requires pool-level sync per the Vulkan spec.
pub open spec fn ts_begin_recording(
    cb_state: CommandBufferState,
    cb_id: nat,
    pool: PoolOwnership,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<CommandBufferState> {
    if can_mutate_pool(pool, thread, reg)
       && pool.children.contains(cb_id)
    {
        // begin_recording internally checks holds_exclusive(reg, cb_id, thread)
        begin_recording(cb_state, cb_id, thread, reg)
    } else {
        None
    }
}

/// Thread-safe vkEndCommandBuffer: same sync requirements as begin.
pub open spec fn ts_end_recording(
    cb_state: CommandBufferState,
    cb_id: nat,
    pool: PoolOwnership,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<CommandBufferState> {
    if can_mutate_pool(pool, thread, reg)
       && pool.children.contains(cb_id)
    {
        end_recording(cb_state, cb_id, thread, reg)
    } else {
        None
    }
}

/// Thread-safe vkResetCommandBuffer: requires exclusive CB access,
/// pool must allow individual reset, and pool must be synced.
pub open spec fn ts_reset_command_buffer(
    cb_state: CommandBufferState,
    cb_id: nat,
    pool: PoolOwnership,
    cmd_pool: CommandPoolState,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<CommandBufferState> {
    if can_mutate_pool(pool, thread, reg)
       && pool.children.contains(cb_id)
       && individual_reset_allowed(cmd_pool, cb_id)
    {
        // reset internally checks holds_exclusive(reg, cb_id, thread)
        reset(cb_state, cb_id, thread, reg)
    } else {
        None
    }
}

// ── Queue Submission ────────────────────────────────────────────────────

/// Thread-safe vkQueueSubmit: requires exclusive access to the queue
/// and (if present) the fence. All submitted CBs must not be exclusively
/// held by another thread.
pub open spec fn ts_submit(
    queue: QueueState,
    info: SubmitInfo,
    cb_states: Map<nat, CommandBufferState>,
    sem_states: Map<nat, SemaphoreState>,
    fence_states: Map<nat, FenceState>,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<(QueueState, SubmissionRecord)> {
    if holds_exclusive(reg, queue.queue_id, thread)
       // If a fence is specified, thread must have exclusive access to it
       && (info.fence_id.is_none()
           || holds_exclusive(reg, info.fence_id.unwrap(), thread))
       // All submitted CBs must not be held by another thread
       && (forall|i: int| #![trigger info.command_buffers[i]]
           0 <= i < info.command_buffers.len() ==>
           not_held_by_other(reg, info.command_buffers[i], thread))
       // Base validation must pass (now includes threading checks)
       && submission_valid(info, cb_states, sem_states, fence_states, queue.queue_id, thread, reg)
    {
        submit_ghost(queue, info, thread, reg)
    } else {
        None
    }
}

// ── Command Pool Operations ─────────────────────────────────────────────

/// Thread-safe vkResetCommandPool: requires exclusive pool access
/// (via PoolOwnership) and no CBs from this pool in Pending state.
///
/// Note: reset_pool_cbs already requires holds_exclusive on the pool.
/// This adds PoolOwnership-level checks and Pending-state validation.
pub open spec fn ts_reset_command_pool(
    pool: CommandPoolState,
    pool_own: PoolOwnership,
    thread: ThreadId,
    reg: TokenRegistry,
    cb_states: Map<nat, CommandBufferState>,
) -> Option<Set<nat>> {
    if can_mutate_pool(pool_own, thread, reg)
       && (forall|cb: nat| pool.allocated_cbs.contains(cb)
           && cb_states.contains_key(cb)
           ==> cb_states[cb] != CommandBufferState::Pending)
    {
        // reset_pool_cbs internally checks holds_exclusive
        reset_pool_cbs(pool, thread, reg)
    } else {
        None
    }
}

/// Thread-safe vkAllocateCommandBuffers: requires exclusive pool access.
pub open spec fn ts_allocate_cb(
    pool: CommandPoolState,
    pool_own: PoolOwnership,
    cb_id: nat,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<CommandPoolState> {
    if can_mutate_pool(pool_own, thread, reg) {
        // allocate_cb internally checks holds_exclusive
        allocate_cb(pool, cb_id, thread, reg)
    } else {
        None
    }
}

/// Thread-safe vkFreeCommandBuffers: requires exclusive pool access,
/// and the CB must not be Pending.
pub open spec fn ts_free_cb(
    pool: CommandPoolState,
    pool_own: PoolOwnership,
    cb_id: nat,
    cb_state: CommandBufferState,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<CommandPoolState> {
    if can_mutate_pool(pool_own, thread, reg)
       && cb_state != CommandBufferState::Pending
       && pool.allocated_cbs.contains(cb_id)
    {
        // free_cb internally checks holds_exclusive
        free_cb(pool, cb_id, thread, reg)
    } else {
        None
    }
}

// ── Descriptor Set Updates ──────────────────────────────────────────────

/// Thread-safe vkUpdateDescriptorSets: the caller must have exclusive
/// access to the destination descriptor set's pool.
///
/// Per the Vulkan spec, the externally synchronized parameter is
/// "dstSet of each element of pDescriptorWrites" — but since sets
/// are allocated from pools, pool-level sync is sufficient.
pub open spec fn ts_update_descriptor_set(
    set: DescriptorSetState,
    writes: Seq<(DescriptorWrite, DescriptorBinding)>,
    pool_own: PoolOwnership,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<DescriptorSetState> {
    if can_access_child(pool_own, set.id, thread, reg) {
        Some(apply_writes(set, writes))
    } else {
        None
    }
}

// ── Queue Family Ownership Transfer ─────────────────────────────────────

/// Thread-safe release barrier: requires exclusive queue access.
pub open spec fn ts_release_ownership(
    ownership: QueueFamilyOwnership,
    src_family: nat,
    dst_family: nat,
    queue_id: nat,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<QueueFamilyOwnership> {
    if holds_exclusive(reg, queue_id, thread) {
        Some(release_ownership(ownership, src_family, dst_family))
    } else {
        None
    }
}

/// Thread-safe acquire barrier: requires exclusive queue access
/// on the destination queue.
pub open spec fn ts_acquire_ownership(
    ownership: QueueFamilyOwnership,
    dst_family: nat,
    queue_id: nat,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<QueueFamilyOwnership> {
    if holds_exclusive(reg, queue_id, thread)
       && transfer_valid(ownership, dst_family)
    {
        Some(acquire_ownership(ownership, dst_family))
    } else {
        None
    }
}

// ═══════════════════════════════════════════════════════════════════════
// Proofs: Thread-safe operations enforce the required invariants
// ═══════════════════════════════════════════════════════════════════════

/// Thread-safe begin_recording guarantees exclusive CB access.
pub proof fn lemma_ts_begin_requires_exclusive_cb(
    cb_state: CommandBufferState,
    cb_id: nat,
    pool: PoolOwnership,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires ts_begin_recording(cb_state, cb_id, pool, thread, reg).is_some(),
    ensures holds_exclusive(reg, cb_id, thread),
{
}

/// Thread-safe begin_recording guarantees exclusive pool access.
pub proof fn lemma_ts_begin_requires_pool_sync(
    cb_state: CommandBufferState,
    cb_id: nat,
    pool: PoolOwnership,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires ts_begin_recording(cb_state, cb_id, pool, thread, reg).is_some(),
    ensures can_mutate_pool(pool, thread, reg),
{
}

/// Thread-safe submit guarantees exclusive queue access.
pub proof fn lemma_ts_submit_requires_queue_exclusive(
    queue: QueueState,
    info: SubmitInfo,
    cb_states: Map<nat, CommandBufferState>,
    sem_states: Map<nat, SemaphoreState>,
    fence_states: Map<nat, FenceState>,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires ts_submit(queue, info, cb_states, sem_states, fence_states, thread, reg).is_some(),
    ensures holds_exclusive(reg, queue.queue_id, thread),
{
}

/// Thread-safe submit blocks other threads from the queue.
pub proof fn lemma_ts_submit_blocks_others(
    queue: QueueState,
    info: SubmitInfo,
    cb_states: Map<nat, CommandBufferState>,
    sem_states: Map<nat, SemaphoreState>,
    fence_states: Map<nat, FenceState>,
    thread: ThreadId,
    other: ThreadId,
    reg: TokenRegistry,
)
    requires
        ts_submit(queue, info, cb_states, sem_states, fence_states, thread, reg).is_some(),
        other != thread,
    ensures
        !holds_exclusive(reg, queue.queue_id, other),
{
}

/// Thread-safe submit ensures all CBs are not held by others.
pub proof fn lemma_ts_submit_cbs_not_held(
    queue: QueueState,
    info: SubmitInfo,
    cb_states: Map<nat, CommandBufferState>,
    sem_states: Map<nat, SemaphoreState>,
    fence_states: Map<nat, FenceState>,
    thread: ThreadId,
    reg: TokenRegistry,
    i: int,
)
    requires
        ts_submit(queue, info, cb_states, sem_states, fence_states, thread, reg).is_some(),
        0 <= i < info.command_buffers.len(),
    ensures
        not_held_by_other(reg, info.command_buffers[i], thread),
{
}

/// Thread-safe submit preserves base validation.
pub proof fn lemma_ts_submit_implies_valid(
    queue: QueueState,
    info: SubmitInfo,
    cb_states: Map<nat, CommandBufferState>,
    sem_states: Map<nat, SemaphoreState>,
    fence_states: Map<nat, FenceState>,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires ts_submit(queue, info, cb_states, sem_states, fence_states, thread, reg).is_some(),
    ensures submission_valid(info, cb_states, sem_states, fence_states, queue.queue_id, thread, reg),
{
}

/// Thread-safe pool reset blocks Pending CBs.
pub proof fn lemma_ts_reset_pool_no_pending(
    pool: CommandPoolState,
    pool_own: PoolOwnership,
    thread: ThreadId,
    reg: TokenRegistry,
    cb_states: Map<nat, CommandBufferState>,
    cb: nat,
)
    requires
        ts_reset_command_pool(pool, pool_own, thread, reg, cb_states).is_some(),
        pool.allocated_cbs.contains(cb),
        cb_states.contains_key(cb),
    ensures
        cb_states[cb] != CommandBufferState::Pending,
{
}

/// Thread-safe descriptor update requires pool access.
pub proof fn lemma_ts_descriptor_update_requires_access(
    set: DescriptorSetState,
    writes: Seq<(DescriptorWrite, DescriptorBinding)>,
    pool_own: PoolOwnership,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires
        ts_update_descriptor_set(set, writes, pool_own, thread, reg).is_some(),
    ensures
        can_access_child(pool_own, set.id, thread, reg),
{
}

/// Thread-safe descriptor update produces the same result as raw.
pub proof fn lemma_ts_descriptor_update_matches_raw(
    set: DescriptorSetState,
    writes: Seq<(DescriptorWrite, DescriptorBinding)>,
    pool_own: PoolOwnership,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires
        ts_update_descriptor_set(set, writes, pool_own, thread, reg).is_some(),
    ensures
        ts_update_descriptor_set(set, writes, pool_own, thread, reg)
            == Some(apply_writes(set, writes)),
{
}

/// Thread-safe release requires exclusive queue access.
pub proof fn lemma_ts_release_requires_queue(
    ownership: QueueFamilyOwnership,
    src_family: nat,
    dst_family: nat,
    queue_id: nat,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires
        ts_release_ownership(ownership, src_family, dst_family, queue_id, thread, reg).is_some(),
    ensures
        holds_exclusive(reg, queue_id, thread),
{
}

/// Two threads recording into different pools is safe:
/// if both hold exclusive access to their own pools, thread 2
/// can't hold thread 1's pool (and vice versa).
pub proof fn lemma_parallel_recording_safe(
    pool1: PoolOwnership,
    pool2: PoolOwnership,
    thread1: ThreadId,
    thread2: ThreadId,
    reg: TokenRegistry,
)
    requires
        thread1 != thread2,
        pool1.pool_id != pool2.pool_id,
        // Both threads hold exclusive access to their own pool
        holds_exclusive(reg, pool1.pool_id, thread1),
        holds_exclusive(reg, pool2.pool_id, thread2),
    ensures
        // Neither thread holds the other's pool
        !holds_exclusive(reg, pool1.pool_id, thread2),
        !holds_exclusive(reg, pool2.pool_id, thread1),
{
    // pool1.pool_id: holder is thread1, so thread2 can't hold it
    // pool2.pool_id: holder is thread2, so thread1 can't hold it
}

/// A thread-safe submit followed by the base check is redundant:
/// ts_submit already enforces submission_valid.
pub proof fn lemma_ts_submit_is_sufficient(
    queue: QueueState,
    info: SubmitInfo,
    cb_states: Map<nat, CommandBufferState>,
    sem_states: Map<nat, SemaphoreState>,
    fence_states: Map<nat, FenceState>,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires ts_submit(queue, info, cb_states, sem_states, fence_states, thread, reg).is_some(),
    ensures ({
        let result = ts_submit(queue, info, cb_states, sem_states, fence_states, thread, reg).unwrap();
        result == submit_ghost(queue, info, thread, reg).unwrap()
    }),
{
}

} // verus!
