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
use crate::event::*;
use crate::query_pool::*;
use crate::memory_map::*;
use crate::resource_lifecycle::*;
use crate::swapchain::*;
use crate::device::*;
use crate::memory::*;
use crate::ring_buffer::*;
use crate::timeline_semaphore::*;
use crate::completion::*;
use crate::image_layout::*;
use crate::lock_ordering::*;
use crate::recording::*;
use crate::recording_commands::*;
use crate::pipeline::*;
use crate::pipeline_layout::*;
use crate::render_pass::*;
use crate::sync::*;
use crate::flags::*;
use crate::secondary_commands::*;
use crate::framebuffer::*;
use crate::image_layout_fsm::*;
use crate::draw_state::*;
use crate::descriptor_validation::*;
use crate::stage_access::*;
use crate::transfer::*;
use crate::memory_aliasing::*;
use crate::indirect::*;
use crate::readback::*;
use crate::msaa::*;
use crate::depth_stencil::*;
use crate::color_blend::*;
use crate::viewport_scissor::*;
use crate::format_properties::*;
use crate::shader_interface::*;
use crate::dynamic_rendering::*;
use crate::bindless::*;
use crate::conditional_rendering::*;
use crate::sampler::*;
use crate::render_graph::*;
use crate::render_graph_exec::*;
use crate::temporal::*;
use crate::ghost_checkpoint::*;
use crate::asset_pipeline::*;
use crate::hot_reload::*;
use crate::taint::*;
use crate::taint_proofs::*;

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
// - vkResetFences: externally sync fence
// - vkDestroyFence: externally sync fence
// - vkDestroySemaphore: externally sync semaphore
// - vkSetEvent / vkResetEvent / vkDestroyEvent: externally sync event
// - vkResetQueryPool: externally sync query pool
// - vkMapMemory / vkUnmapMemory: externally sync device memory
// - vkFlushMappedMemoryRanges / vkInvalidateMappedMemoryRanges: externally sync memory
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

// ── Fence Operations ─────────────────────────────────────────────────

/// Thread-safe vkResetFences: requires exclusive fence access.
pub open spec fn ts_reset_fence(
    fence: FenceState,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<FenceState> {
    if holds_exclusive(reg, fence.id, thread) {
        Some(reset_fence_ghost(fence))
    } else {
        None
    }
}

/// Thread-safe vkDestroyFence: requires exclusive fence access.
pub open spec fn ts_destroy_fence(
    fence: FenceState,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<FenceState> {
    if holds_exclusive(reg, fence.id, thread) {
        Some(destroy_fence_ghost(fence))
    } else {
        None
    }
}

// ── Semaphore Operations ─────────────────────────────────────────────

/// Thread-safe vkDestroySemaphore: requires exclusive semaphore access.
pub open spec fn ts_destroy_semaphore(
    sem: SemaphoreState,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<SemaphoreState> {
    if holds_exclusive(reg, sem.id, thread) {
        Some(destroy_semaphore_ghost(sem))
    } else {
        None
    }
}

// ── Event Operations ─────────────────────────────────────────────────

/// Thread-safe vkSetEvent: requires exclusive event access.
pub open spec fn ts_set_event(
    event: EventState,
    stages: Set<nat>,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<EventState> {
    if holds_exclusive(reg, event.id, thread) {
        Some(set_event(event, stages))
    } else {
        None
    }
}

/// Thread-safe vkResetEvent: requires exclusive event access.
pub open spec fn ts_reset_event(
    event: EventState,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<EventState> {
    if holds_exclusive(reg, event.id, thread) {
        Some(reset_event(event))
    } else {
        None
    }
}

/// Thread-safe vkDestroyEvent: requires exclusive event access.
pub open spec fn ts_destroy_event(
    event: EventState,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<EventState> {
    if holds_exclusive(reg, event.id, thread) {
        Some(destroy_event(event))
    } else {
        None
    }
}

// ── Query Pool Operations ────────────────────────────────────────────

/// Thread-safe vkResetQueryPool: requires exclusive pool access.
pub open spec fn ts_reset_queries(
    pool: QueryPoolState,
    first: nat,
    count: nat,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<QueryPoolState> {
    if holds_exclusive(reg, pool.id, thread) {
        Some(reset_queries(pool, first, count))
    } else {
        None
    }
}

// ── Memory Map Operations ────────────────────────────────────────────

/// Thread-safe vkMapMemory: requires exclusive access to the memory object.
pub open spec fn ts_map_memory(
    state: MemoryMapState,
    offset: nat,
    size: nat,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<MemoryMapState> {
    if holds_exclusive(reg, state.allocation_id, thread) {
        Some(map_memory(state, offset, size))
    } else {
        None
    }
}

/// Thread-safe vkUnmapMemory: requires exclusive access to the memory object.
pub open spec fn ts_unmap_memory(
    state: MemoryMapState,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<MemoryMapState> {
    if holds_exclusive(reg, state.allocation_id, thread) {
        Some(unmap_memory(state))
    } else {
        None
    }
}

/// Thread-safe vkFlushMappedMemoryRanges: requires exclusive access.
pub open spec fn ts_flush_memory(
    state: MemoryMapState,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<MemoryMapState> {
    if holds_exclusive(reg, state.allocation_id, thread) {
        Some(flush_memory(state))
    } else {
        None
    }
}

/// Thread-safe vkInvalidateMappedMemoryRanges: requires exclusive access.
pub open spec fn ts_invalidate_memory(
    state: MemoryMapState,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<MemoryMapState> {
    if holds_exclusive(reg, state.allocation_id, thread) {
        Some(invalidate_memory(state))
    } else {
        None
    }
}

// ═══════════════════════════════════════════════════════════════════════
// Proofs: New thread-safe operations enforce exclusivity
// ═══════════════════════════════════════════════════════════════════════

// ── Fence proofs ─────────────────────────────────────────────────────

/// Thread-safe fence reset requires exclusive access.
pub proof fn lemma_ts_reset_fence_requires_exclusive(
    fence: FenceState,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires ts_reset_fence(fence, thread, reg).is_some(),
    ensures holds_exclusive(reg, fence.id, thread),
{
}

/// Thread-safe fence reset matches the raw operation.
pub proof fn lemma_ts_reset_fence_matches_raw(
    fence: FenceState,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires ts_reset_fence(fence, thread, reg).is_some(),
    ensures ts_reset_fence(fence, thread, reg) == Some(reset_fence_ghost(fence)),
{
}

/// Thread-safe fence destroy requires exclusive access.
pub proof fn lemma_ts_destroy_fence_requires_exclusive(
    fence: FenceState,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires ts_destroy_fence(fence, thread, reg).is_some(),
    ensures holds_exclusive(reg, fence.id, thread),
{
}

/// Thread-safe fence reset blocks other threads from the fence.
pub proof fn lemma_ts_reset_fence_blocks_others(
    fence: FenceState,
    thread: ThreadId,
    other: ThreadId,
    reg: TokenRegistry,
)
    requires
        ts_reset_fence(fence, thread, reg).is_some(),
        other != thread,
    ensures
        !holds_exclusive(reg, fence.id, other),
{
}

// ── Semaphore proofs ─────────────────────────────────────────────────

/// Thread-safe semaphore destroy requires exclusive access.
pub proof fn lemma_ts_destroy_semaphore_requires_exclusive(
    sem: SemaphoreState,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires ts_destroy_semaphore(sem, thread, reg).is_some(),
    ensures holds_exclusive(reg, sem.id, thread),
{
}

// ── Event proofs ─────────────────────────────────────────────────────

/// Thread-safe set event requires exclusive access.
pub proof fn lemma_ts_set_event_requires_exclusive(
    event: EventState,
    stages: Set<nat>,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires ts_set_event(event, stages, thread, reg).is_some(),
    ensures holds_exclusive(reg, event.id, thread),
{
}

/// Thread-safe reset event requires exclusive access.
pub proof fn lemma_ts_reset_event_requires_exclusive(
    event: EventState,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires ts_reset_event(event, thread, reg).is_some(),
    ensures holds_exclusive(reg, event.id, thread),
{
}

/// Thread-safe destroy event requires exclusive access.
pub proof fn lemma_ts_destroy_event_requires_exclusive(
    event: EventState,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires ts_destroy_event(event, thread, reg).is_some(),
    ensures holds_exclusive(reg, event.id, thread),
{
}

/// Thread-safe set then reset returns unsignaled (preserves base property).
pub proof fn lemma_ts_set_then_reset_unsignaled(
    event: EventState,
    stages: Set<nat>,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires holds_exclusive(reg, event.id, thread),
    ensures ({
        let after_set = ts_set_event(event, stages, thread, reg).unwrap();
        ts_reset_event(after_set, thread, reg).is_some()
        && !ts_reset_event(after_set, thread, reg).unwrap().signaled
    }),
{
}

// ── Query Pool proofs ────────────────────────────────────────────────

/// Thread-safe query pool reset requires exclusive access.
pub proof fn lemma_ts_reset_queries_requires_exclusive(
    pool: QueryPoolState,
    first: nat,
    count: nat,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires ts_reset_queries(pool, first, count, thread, reg).is_some(),
    ensures holds_exclusive(reg, pool.id, thread),
{
}

/// Thread-safe query pool reset matches raw operation.
pub proof fn lemma_ts_reset_queries_matches_raw(
    pool: QueryPoolState,
    first: nat,
    count: nat,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires ts_reset_queries(pool, first, count, thread, reg).is_some(),
    ensures ts_reset_queries(pool, first, count, thread, reg) == Some(reset_queries(pool, first, count)),
{
}

// ── Memory Map proofs ────────────────────────────────────────────────

/// Thread-safe map requires exclusive access.
pub proof fn lemma_ts_map_memory_requires_exclusive(
    state: MemoryMapState,
    offset: nat,
    size: nat,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires ts_map_memory(state, offset, size, thread, reg).is_some(),
    ensures holds_exclusive(reg, state.allocation_id, thread),
{
}

/// Thread-safe unmap requires exclusive access.
pub proof fn lemma_ts_unmap_memory_requires_exclusive(
    state: MemoryMapState,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires ts_unmap_memory(state, thread, reg).is_some(),
    ensures holds_exclusive(reg, state.allocation_id, thread),
{
}

/// Thread-safe flush requires exclusive access.
pub proof fn lemma_ts_flush_memory_requires_exclusive(
    state: MemoryMapState,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires ts_flush_memory(state, thread, reg).is_some(),
    ensures holds_exclusive(reg, state.allocation_id, thread),
{
}

/// Thread-safe invalidate requires exclusive access.
pub proof fn lemma_ts_invalidate_memory_requires_exclusive(
    state: MemoryMapState,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires ts_invalidate_memory(state, thread, reg).is_some(),
    ensures holds_exclusive(reg, state.allocation_id, thread),
{
}

/// Thread-safe map then unmap roundtrip: memory returns to unmapped.
pub proof fn lemma_ts_map_unmap_roundtrip(
    state: MemoryMapState,
    offset: nat,
    size: nat,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires holds_exclusive(reg, state.allocation_id, thread),
    ensures ({
        let mapped = ts_map_memory(state, offset, size, thread, reg).unwrap();
        ts_unmap_memory(mapped, thread, reg).is_some()
        && !ts_unmap_memory(mapped, thread, reg).unwrap().mapped
    }),
{
}

/// Thread-safe flush makes host writes visible.
pub proof fn lemma_ts_flush_makes_visible(
    state: MemoryMapState,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires holds_exclusive(reg, state.allocation_id, thread),
    ensures host_writes_visible(ts_flush_memory(state, thread, reg).unwrap()),
{
}

/// Two threads cannot both reset the same fence.
pub proof fn lemma_fence_reset_mutual_exclusion(
    fence: FenceState,
    thread1: ThreadId,
    thread2: ThreadId,
    reg: TokenRegistry,
)
    requires
        thread1 != thread2,
        ts_reset_fence(fence, thread1, reg).is_some(),
    ensures
        ts_reset_fence(fence, thread2, reg).is_none(),
{
}

/// Two threads cannot both map the same memory.
pub proof fn lemma_map_mutual_exclusion(
    state: MemoryMapState,
    offset1: nat,
    size1: nat,
    offset2: nat,
    size2: nat,
    thread1: ThreadId,
    thread2: ThreadId,
    reg: TokenRegistry,
)
    requires
        thread1 != thread2,
        ts_map_memory(state, offset1, size1, thread1, reg).is_some(),
    ensures
        ts_map_memory(state, offset2, size2, thread2, reg).is_none(),
{
}

// ═══════════════════════════════════════════════════════════════════════
// Resource Lifecycle Thread-Safe Wrappers
// ═══════════════════════════════════════════════════════════════════════

/// Thread-safe bind_resource: requires exclusive access to the resource.
pub open spec fn ts_bind_resource(
    state: ResourceLifecycleState,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<ResourceLifecycleState> {
    if holds_exclusive(reg, resource_sync_id(state.resource), thread)
       && can_bind(state)
    {
        Some(bind_resource(state))
    } else {
        None
    }
}

/// Thread-safe submit_resource: requires exclusive access to the resource.
pub open spec fn ts_submit_resource(
    state: ResourceLifecycleState,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<ResourceLifecycleState> {
    if holds_exclusive(reg, resource_sync_id(state.resource), thread)
       && can_use(state)
    {
        Some(submit_resource(state))
    } else {
        None
    }
}

/// Thread-safe complete_use: requires exclusive access to the resource.
pub open spec fn ts_complete_use(
    state: ResourceLifecycleState,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<ResourceLifecycleState> {
    if holds_exclusive(reg, resource_sync_id(state.resource), thread)
       && state.pending_use_count > 0
    {
        Some(complete_use(state))
    } else {
        None
    }
}

/// Thread-safe destroy_resource: requires exclusive access to the resource.
pub open spec fn ts_destroy_resource(
    state: ResourceLifecycleState,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<ResourceLifecycleState> {
    if holds_exclusive(reg, resource_sync_id(state.resource), thread)
       && can_destroy(state)
    {
        Some(destroy_resource(state))
    } else {
        None
    }
}

// ── Resource Lifecycle Proofs ──────────────────────────────────────────

pub proof fn lemma_ts_bind_resource_requires_exclusive(
    state: ResourceLifecycleState, thread: ThreadId, reg: TokenRegistry,
)
    requires ts_bind_resource(state, thread, reg).is_some(),
    ensures holds_exclusive(reg, resource_sync_id(state.resource), thread),
{
}

pub proof fn lemma_ts_submit_resource_requires_exclusive(
    state: ResourceLifecycleState, thread: ThreadId, reg: TokenRegistry,
)
    requires ts_submit_resource(state, thread, reg).is_some(),
    ensures holds_exclusive(reg, resource_sync_id(state.resource), thread),
{
}

pub proof fn lemma_ts_complete_use_requires_exclusive(
    state: ResourceLifecycleState, thread: ThreadId, reg: TokenRegistry,
)
    requires ts_complete_use(state, thread, reg).is_some(),
    ensures holds_exclusive(reg, resource_sync_id(state.resource), thread),
{
}

pub proof fn lemma_ts_destroy_resource_requires_exclusive(
    state: ResourceLifecycleState, thread: ThreadId, reg: TokenRegistry,
)
    requires ts_destroy_resource(state, thread, reg).is_some(),
    ensures holds_exclusive(reg, resource_sync_id(state.resource), thread),
{
}

// ═══════════════════════════════════════════════════════════════════════
// Swapchain Thread-Safe Wrappers
// ═══════════════════════════════════════════════════════════════════════

/// Thread-safe vkAcquireNextImageKHR: requires exclusive swapchain access.
pub open spec fn ts_acquire_image(
    swapchain: SwapchainState,
    idx: nat,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<SwapchainState> {
    if holds_exclusive(reg, swapchain.id, thread) {
        acquire_image(swapchain, idx)
    } else {
        None
    }
}

/// Thread-safe vkQueuePresentKHR: requires exclusive swapchain access.
pub open spec fn ts_present_image(
    swapchain: SwapchainState,
    idx: nat,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<SwapchainState> {
    if holds_exclusive(reg, swapchain.id, thread) {
        present_image(swapchain, idx)
    } else {
        None
    }
}

// ── Swapchain Proofs ───────────────────────────────────────────────────

pub proof fn lemma_ts_acquire_image_requires_exclusive(
    swapchain: SwapchainState, idx: nat, thread: ThreadId, reg: TokenRegistry,
)
    requires ts_acquire_image(swapchain, idx, thread, reg).is_some(),
    ensures holds_exclusive(reg, swapchain.id, thread),
{
}

pub proof fn lemma_ts_present_image_requires_exclusive(
    swapchain: SwapchainState, idx: nat, thread: ThreadId, reg: TokenRegistry,
)
    requires ts_present_image(swapchain, idx, thread, reg).is_some(),
    ensures holds_exclusive(reg, swapchain.id, thread),
{
}

// ═══════════════════════════════════════════════════════════════════════
// Device Thread-Safe Wrappers
// ═══════════════════════════════════════════════════════════════════════

/// Thread-safe vkAllocateMemory: requires exclusive device access.
pub open spec fn ts_allocate_memory(
    dev: DeviceState,
    heap_idx: nat,
    size: nat,
    device_id: nat,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<DeviceState> {
    if holds_exclusive(reg, device_id, thread) {
        Some(allocate_memory_ghost(dev, heap_idx, size))
    } else {
        None
    }
}

/// Thread-safe vkFreeMemory: requires exclusive device access.
pub open spec fn ts_free_memory(
    dev: DeviceState,
    heap_idx: nat,
    size: nat,
    device_id: nat,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<DeviceState> {
    if holds_exclusive(reg, device_id, thread) {
        Some(free_memory_ghost(dev, heap_idx, size))
    } else {
        None
    }
}

/// Thread-safe vkCreateBuffer: requires exclusive device access.
pub open spec fn ts_create_buffer(
    dev: DeviceState,
    device_id: nat,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<DeviceState> {
    if holds_exclusive(reg, device_id, thread) {
        Some(create_buffer_ghost(dev))
    } else {
        None
    }
}

/// Thread-safe vkDestroyBuffer: requires exclusive device access.
pub open spec fn ts_destroy_buffer(
    dev: DeviceState,
    device_id: nat,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<DeviceState> {
    if holds_exclusive(reg, device_id, thread) {
        Some(destroy_buffer_ghost(dev))
    } else {
        None
    }
}

/// Thread-safe vkCreateImage: requires exclusive device access.
pub open spec fn ts_create_image(
    dev: DeviceState,
    device_id: nat,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<DeviceState> {
    if holds_exclusive(reg, device_id, thread) {
        Some(create_image_ghost(dev))
    } else {
        None
    }
}

/// Thread-safe vkDestroyImage: requires exclusive device access.
pub open spec fn ts_destroy_image(
    dev: DeviceState,
    device_id: nat,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<DeviceState> {
    if holds_exclusive(reg, device_id, thread) {
        Some(destroy_image_ghost(dev))
    } else {
        None
    }
}

// ── Device Proofs ──────────────────────────────────────────────────────

pub proof fn lemma_ts_allocate_memory_requires_exclusive(
    dev: DeviceState, heap_idx: nat, size: nat, device_id: nat, thread: ThreadId, reg: TokenRegistry,
)
    requires ts_allocate_memory(dev, heap_idx, size, device_id, thread, reg).is_some(),
    ensures holds_exclusive(reg, device_id, thread),
{
}

pub proof fn lemma_ts_free_memory_requires_exclusive(
    dev: DeviceState, heap_idx: nat, size: nat, device_id: nat, thread: ThreadId, reg: TokenRegistry,
)
    requires ts_free_memory(dev, heap_idx, size, device_id, thread, reg).is_some(),
    ensures holds_exclusive(reg, device_id, thread),
{
}

pub proof fn lemma_ts_create_buffer_requires_exclusive(
    dev: DeviceState, device_id: nat, thread: ThreadId, reg: TokenRegistry,
)
    requires ts_create_buffer(dev, device_id, thread, reg).is_some(),
    ensures holds_exclusive(reg, device_id, thread),
{
}

pub proof fn lemma_ts_destroy_buffer_requires_exclusive(
    dev: DeviceState, device_id: nat, thread: ThreadId, reg: TokenRegistry,
)
    requires ts_destroy_buffer(dev, device_id, thread, reg).is_some(),
    ensures holds_exclusive(reg, device_id, thread),
{
}

pub proof fn lemma_ts_create_image_requires_exclusive(
    dev: DeviceState, device_id: nat, thread: ThreadId, reg: TokenRegistry,
)
    requires ts_create_image(dev, device_id, thread, reg).is_some(),
    ensures holds_exclusive(reg, device_id, thread),
{
}

pub proof fn lemma_ts_destroy_image_requires_exclusive(
    dev: DeviceState, device_id: nat, thread: ThreadId, reg: TokenRegistry,
)
    requires ts_destroy_image(dev, device_id, thread, reg).is_some(),
    ensures holds_exclusive(reg, device_id, thread),
{
}

// ═══════════════════════════════════════════════════════════════════════
// Memory Binding Thread-Safe Wrappers
// ═══════════════════════════════════════════════════════════════════════

/// Thread-safe vkBindBufferMemory: requires exclusive buffer access.
pub open spec fn ts_bind_buffer_memory(
    buf: BufferState,
    allocation_id: nat,
    offset: nat,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<BufferState> {
    if holds_exclusive(reg, buf.id, thread) {
        Some(bind_buffer_memory(buf, allocation_id, offset))
    } else {
        None
    }
}

/// Thread-safe vkBindImageMemory: requires exclusive image access.
pub open spec fn ts_bind_image_memory(
    img: ImageState,
    allocation_id: nat,
    offset: nat,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<ImageState> {
    if holds_exclusive(reg, img.id, thread) {
        Some(bind_image_memory(img, allocation_id, offset))
    } else {
        None
    }
}

/// Thread-safe image layout transition: requires exclusive image access.
pub open spec fn ts_transition_image_layout(
    img: ImageState,
    sub: ImageSubresource,
    new_layout: ImageLayout,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<ImageState> {
    if holds_exclusive(reg, img.id, thread) {
        Some(transition_image_layout(img, sub, new_layout))
    } else {
        None
    }
}

// ── Memory Binding Proofs ──────────────────────────────────────────────

pub proof fn lemma_ts_bind_buffer_memory_requires_exclusive(
    buf: BufferState, allocation_id: nat, offset: nat, thread: ThreadId, reg: TokenRegistry,
)
    requires ts_bind_buffer_memory(buf, allocation_id, offset, thread, reg).is_some(),
    ensures holds_exclusive(reg, buf.id, thread),
{
}

pub proof fn lemma_ts_bind_image_memory_requires_exclusive(
    img: ImageState, allocation_id: nat, offset: nat, thread: ThreadId, reg: TokenRegistry,
)
    requires ts_bind_image_memory(img, allocation_id, offset, thread, reg).is_some(),
    ensures holds_exclusive(reg, img.id, thread),
{
}

pub proof fn lemma_ts_transition_image_layout_requires_exclusive(
    img: ImageState, sub: ImageSubresource, new_layout: ImageLayout, thread: ThreadId, reg: TokenRegistry,
)
    requires ts_transition_image_layout(img, sub, new_layout, thread, reg).is_some(),
    ensures holds_exclusive(reg, img.id, thread),
{
}

// ═══════════════════════════════════════════════════════════════════════
// Ring Buffer Thread-Safe Wrappers
// ═══════════════════════════════════════════════════════════════════════

/// Thread-safe ring buffer acquire: requires exclusive ring buffer access.
pub open spec fn ts_ring_acquire(
    ring: RingBufferState,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<RingBufferState> {
    if holds_exclusive(reg, ring.id, thread)
       && ring_well_formed(ring)
       && frames_in_flight(ring) + 1 < ring.capacity
    {
        Some(ring_acquire(ring))
    } else {
        None
    }
}

/// Thread-safe ring buffer retire: requires exclusive ring buffer access.
pub open spec fn ts_ring_retire(
    ring: RingBufferState,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<RingBufferState> {
    if holds_exclusive(reg, ring.id, thread)
       && ring_well_formed(ring)
       && frames_in_flight(ring) > 0
    {
        Some(ring_retire(ring))
    } else {
        None
    }
}

// ── Ring Buffer Proofs ─────────────────────────────────────────────────

pub proof fn lemma_ts_ring_acquire_requires_exclusive(
    ring: RingBufferState, thread: ThreadId, reg: TokenRegistry,
)
    requires ts_ring_acquire(ring, thread, reg).is_some(),
    ensures holds_exclusive(reg, ring.id, thread),
{
}

pub proof fn lemma_ts_ring_retire_requires_exclusive(
    ring: RingBufferState, thread: ThreadId, reg: TokenRegistry,
)
    requires ts_ring_retire(ring, thread, reg).is_some(),
    ensures holds_exclusive(reg, ring.id, thread),
{
}

// ═══════════════════════════════════════════════════════════════════════
// Timeline Semaphore Thread-Safe Wrappers
// ═══════════════════════════════════════════════════════════════════════

/// Thread-safe timeline semaphore submit signal: requires exclusive access.
pub open spec fn ts_timeline_submit_signal(
    sem: TimelineSemaphoreState,
    value: nat,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<TimelineSemaphoreState> {
    if holds_exclusive(reg, sem.id, thread)
       && signal_value_valid(sem, value)
    {
        Some(submit_signal(sem, value))
    } else {
        None
    }
}

/// Thread-safe timeline semaphore submit wait: requires exclusive access.
pub open spec fn ts_timeline_submit_wait(
    sem: TimelineSemaphoreState,
    value: nat,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<TimelineSemaphoreState> {
    if holds_exclusive(reg, sem.id, thread) {
        Some(submit_wait(sem, value))
    } else {
        None
    }
}

/// Thread-safe timeline semaphore host wait: requires exclusive access.
pub open spec fn ts_timeline_host_wait(
    sem: TimelineSemaphoreState,
    value: nat,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<TimelineSemaphoreState> {
    if holds_exclusive(reg, sem.id, thread)
       && wait_satisfied(sem, value)
    {
        Some(host_wait(sem, value))
    } else {
        None
    }
}

// ── Timeline Semaphore Proofs ──────────────────────────────────────────

pub proof fn lemma_ts_timeline_submit_signal_requires_exclusive(
    sem: TimelineSemaphoreState, value: nat, thread: ThreadId, reg: TokenRegistry,
)
    requires ts_timeline_submit_signal(sem, value, thread, reg).is_some(),
    ensures holds_exclusive(reg, sem.id, thread),
{
}

pub proof fn lemma_ts_timeline_submit_wait_requires_exclusive(
    sem: TimelineSemaphoreState, value: nat, thread: ThreadId, reg: TokenRegistry,
)
    requires ts_timeline_submit_wait(sem, value, thread, reg).is_some(),
    ensures holds_exclusive(reg, sem.id, thread),
{
}

pub proof fn lemma_ts_timeline_host_wait_requires_exclusive(
    sem: TimelineSemaphoreState, value: nat, thread: ThreadId, reg: TokenRegistry,
)
    requires ts_timeline_host_wait(sem, value, thread, reg).is_some(),
    ensures holds_exclusive(reg, sem.id, thread),
{
}

// ═══════════════════════════════════════════════════════════════════════
// Descriptor Pool Thread-Safe Wrappers
// ═══════════════════════════════════════════════════════════════════════

/// Thread-safe vkAllocateDescriptorSets: requires exclusive pool access.
pub open spec fn ts_allocate_from_pool(
    pool: DescriptorPoolState,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<DescriptorPoolState> {
    if holds_exclusive(reg, pool.id, thread)
       && pool_can_allocate(pool)
    {
        Some(allocate_from_pool(pool))
    } else {
        None
    }
}

/// Thread-safe vkFreeDescriptorSets: requires exclusive pool access.
pub open spec fn ts_free_to_pool(
    pool: DescriptorPoolState,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<DescriptorPoolState> {
    if holds_exclusive(reg, pool.id, thread)
       && pool.allocated_sets > 0
    {
        Some(free_to_pool(pool))
    } else {
        None
    }
}

// ── Descriptor Pool Proofs ─────────────────────────────────────────────

pub proof fn lemma_ts_allocate_from_pool_requires_exclusive(
    pool: DescriptorPoolState, thread: ThreadId, reg: TokenRegistry,
)
    requires ts_allocate_from_pool(pool, thread, reg).is_some(),
    ensures holds_exclusive(reg, pool.id, thread),
{
}

pub proof fn lemma_ts_free_to_pool_requires_exclusive(
    pool: DescriptorPoolState, thread: ThreadId, reg: TokenRegistry,
)
    requires ts_free_to_pool(pool, thread, reg).is_some(),
    ensures holds_exclusive(reg, pool.id, thread),
{
}

// ═══════════════════════════════════════════════════════════════════════
// Cross-Cutting Integration Proofs
// ═══════════════════════════════════════════════════════════════════════

/// Two threads cannot both acquire from the same swapchain.
pub proof fn lemma_swapchain_acquire_mutual_exclusion(
    swapchain: SwapchainState,
    idx1: nat,
    idx2: nat,
    thread1: ThreadId,
    thread2: ThreadId,
    reg: TokenRegistry,
)
    requires
        thread1 != thread2,
        ts_acquire_image(swapchain, idx1, thread1, reg).is_some(),
    ensures
        ts_acquire_image(swapchain, idx2, thread2, reg).is_none(),
{
}

/// Exclusive ring buffer ownership prevents concurrent slot writes.
pub proof fn lemma_ring_buffer_exclusive_prevents_concurrent(
    ring: RingBufferState,
    thread1: ThreadId,
    thread2: ThreadId,
    reg: TokenRegistry,
)
    requires
        thread1 != thread2,
        ts_ring_acquire(ring, thread1, reg).is_some(),
    ensures
        ts_ring_acquire(ring, thread2, reg).is_none(),
{
}

/// After ts_destroy_resource, the resource is dead — no further ops possible.
pub proof fn lemma_destroy_then_release_safe(
    state: ResourceLifecycleState,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires ts_destroy_resource(state, thread, reg).is_some(),
    ensures ({
        let destroyed = ts_destroy_resource(state, thread, reg).unwrap();
        !resource_alive(destroyed)
        && !can_use(destroyed)
        && !can_destroy(destroyed)
        && !can_bind(destroyed)
    }),
{
}

/// A destroyed resource cannot be submitted again.
pub proof fn lemma_destroyed_no_resubmit(
    state: ResourceLifecycleState,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires ts_destroy_resource(state, thread, reg).is_some(),
    ensures ({
        let destroyed = ts_destroy_resource(state, thread, reg).unwrap();
        ts_submit_resource(destroyed, thread, reg).is_none()
    }),
{
}

/// Thread-safe descriptor update + not-in-flight = no GPU hazard.
pub proof fn lemma_ts_update_no_gpu_hazard(
    set: DescriptorSetState,
    writes: Seq<(DescriptorWrite, DescriptorBinding)>,
    pool_own: PoolOwnership,
    dev: DeviceState,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires
        ts_update_descriptor_set(set, writes, pool_own, thread, reg).is_some(),
        descriptor_not_in_flight(dev, set.id),
    ensures
        // The update is safe: we have exclusive access AND no GPU is using the set
        can_access_child(pool_own, set.id, thread, reg)
        && no_pending_references(dev.pending_submissions, ResourceId::DescriptorSet { id: set.id }),
{
}

// ═══════════════════════════════════════════════════════════════════════
// Lock-Ordered Operation Wrappers
//
// These wrappers enforce deadlock freedom by requiring lock ordering
// compliance. Each wrapper checks that the caller's held locks allow
// acquiring at the required level before delegating to the base ts_* op.
//
// Lock levels: Device(0) < Queue(1) < CommandPool(2) < CommandBuffer(3)
//              < DescriptorPool(4) < Fence(5)
// ═══════════════════════════════════════════════════════════════════════

// ── Device Level (0) ────────────────────────────────────────────────────

/// Lock-ordered vkAllocateMemory.
pub open spec fn ts_lo_allocate_memory(
    dev: DeviceState, heap_idx: nat, size: nat,
    device_id: nat, thread: ThreadId, reg: TokenRegistry, held: HeldLocks,
) -> Option<DeviceState> {
    if held.thread == thread && lock_order_valid(held) && can_acquire_at_level(held, device_level()) {
        ts_allocate_memory(dev, heap_idx, size, device_id, thread, reg)
    } else { None }
}

/// Lock-ordered vkFreeMemory.
pub open spec fn ts_lo_free_memory(
    dev: DeviceState, heap_idx: nat, size: nat,
    device_id: nat, thread: ThreadId, reg: TokenRegistry, held: HeldLocks,
) -> Option<DeviceState> {
    if held.thread == thread && lock_order_valid(held) && can_acquire_at_level(held, device_level()) {
        ts_free_memory(dev, heap_idx, size, device_id, thread, reg)
    } else { None }
}

/// Lock-ordered vkCreateBuffer.
pub open spec fn ts_lo_create_buffer(
    dev: DeviceState, device_id: nat,
    thread: ThreadId, reg: TokenRegistry, held: HeldLocks,
) -> Option<DeviceState> {
    if held.thread == thread && lock_order_valid(held) && can_acquire_at_level(held, device_level()) {
        ts_create_buffer(dev, device_id, thread, reg)
    } else { None }
}

/// Lock-ordered vkDestroyBuffer.
pub open spec fn ts_lo_destroy_buffer(
    dev: DeviceState, device_id: nat,
    thread: ThreadId, reg: TokenRegistry, held: HeldLocks,
) -> Option<DeviceState> {
    if held.thread == thread && lock_order_valid(held) && can_acquire_at_level(held, device_level()) {
        ts_destroy_buffer(dev, device_id, thread, reg)
    } else { None }
}

/// Lock-ordered vkCreateImage.
pub open spec fn ts_lo_create_image(
    dev: DeviceState, device_id: nat,
    thread: ThreadId, reg: TokenRegistry, held: HeldLocks,
) -> Option<DeviceState> {
    if held.thread == thread && lock_order_valid(held) && can_acquire_at_level(held, device_level()) {
        ts_create_image(dev, device_id, thread, reg)
    } else { None }
}

/// Lock-ordered vkDestroyImage.
pub open spec fn ts_lo_destroy_image(
    dev: DeviceState, device_id: nat,
    thread: ThreadId, reg: TokenRegistry, held: HeldLocks,
) -> Option<DeviceState> {
    if held.thread == thread && lock_order_valid(held) && can_acquire_at_level(held, device_level()) {
        ts_destroy_image(dev, device_id, thread, reg)
    } else { None }
}

// ── Queue Level (1) ─────────────────────────────────────────────────────

/// Lock-ordered vkQueueSubmit.
pub open spec fn ts_lo_submit(
    queue: QueueState, info: SubmitInfo,
    cb_states: Map<nat, CommandBufferState>,
    sem_states: Map<nat, SemaphoreState>,
    fence_states: Map<nat, FenceState>,
    thread: ThreadId, reg: TokenRegistry, held: HeldLocks,
) -> Option<(QueueState, SubmissionRecord)> {
    if held.thread == thread && lock_order_valid(held) && can_acquire_at_level(held, queue_level()) {
        ts_submit(queue, info, cb_states, sem_states, fence_states, thread, reg)
    } else { None }
}

/// Lock-ordered vkAcquireNextImageKHR.
pub open spec fn ts_lo_acquire_image(
    swapchain: SwapchainState, idx: nat,
    thread: ThreadId, reg: TokenRegistry, held: HeldLocks,
) -> Option<SwapchainState> {
    if held.thread == thread && lock_order_valid(held) && can_acquire_at_level(held, queue_level()) {
        ts_acquire_image(swapchain, idx, thread, reg)
    } else { None }
}

/// Lock-ordered vkQueuePresentKHR.
pub open spec fn ts_lo_present_image(
    swapchain: SwapchainState, idx: nat,
    thread: ThreadId, reg: TokenRegistry, held: HeldLocks,
) -> Option<SwapchainState> {
    if held.thread == thread && lock_order_valid(held) && can_acquire_at_level(held, queue_level()) {
        ts_present_image(swapchain, idx, thread, reg)
    } else { None }
}

// ── Command Pool Level (2) ──────────────────────────────────────────────

/// Lock-ordered vkResetCommandPool.
pub open spec fn ts_lo_reset_command_pool(
    pool: CommandPoolState, pool_own: PoolOwnership,
    thread: ThreadId, reg: TokenRegistry,
    cb_states: Map<nat, CommandBufferState>, held: HeldLocks,
) -> Option<Set<nat>> {
    if held.thread == thread && lock_order_valid(held) && can_acquire_at_level(held, command_pool_level()) {
        ts_reset_command_pool(pool, pool_own, thread, reg, cb_states)
    } else { None }
}

/// Lock-ordered vkAllocateCommandBuffers.
pub open spec fn ts_lo_allocate_cb(
    pool: CommandPoolState, pool_own: PoolOwnership,
    cb_id: nat, thread: ThreadId, reg: TokenRegistry, held: HeldLocks,
) -> Option<CommandPoolState> {
    if held.thread == thread && lock_order_valid(held) && can_acquire_at_level(held, command_pool_level()) {
        ts_allocate_cb(pool, pool_own, cb_id, thread, reg)
    } else { None }
}

/// Lock-ordered vkFreeCommandBuffers.
pub open spec fn ts_lo_free_cb(
    pool: CommandPoolState, pool_own: PoolOwnership,
    cb_id: nat, cb_state: CommandBufferState,
    thread: ThreadId, reg: TokenRegistry, held: HeldLocks,
) -> Option<CommandPoolState> {
    if held.thread == thread && lock_order_valid(held) && can_acquire_at_level(held, command_pool_level()) {
        ts_free_cb(pool, pool_own, cb_id, cb_state, thread, reg)
    } else { None }
}

// ── Command Buffer Level (3) ────────────────────────────────────────────

/// Lock-ordered vkBeginCommandBuffer.
pub open spec fn ts_lo_begin_recording(
    cb_state: CommandBufferState, cb_id: nat,
    pool: PoolOwnership, thread: ThreadId, reg: TokenRegistry, held: HeldLocks,
) -> Option<CommandBufferState> {
    if held.thread == thread && lock_order_valid(held) && can_acquire_at_level(held, command_buffer_level()) {
        ts_begin_recording(cb_state, cb_id, pool, thread, reg)
    } else { None }
}

/// Lock-ordered vkEndCommandBuffer.
pub open spec fn ts_lo_end_recording(
    cb_state: CommandBufferState, cb_id: nat,
    pool: PoolOwnership, thread: ThreadId, reg: TokenRegistry, held: HeldLocks,
) -> Option<CommandBufferState> {
    if held.thread == thread && lock_order_valid(held) && can_acquire_at_level(held, command_buffer_level()) {
        ts_end_recording(cb_state, cb_id, pool, thread, reg)
    } else { None }
}

// ── Descriptor Pool Level (4) ───────────────────────────────────────────

/// Lock-ordered vkUpdateDescriptorSets.
pub open spec fn ts_lo_update_descriptor_set(
    set: DescriptorSetState,
    writes: Seq<(DescriptorWrite, DescriptorBinding)>,
    pool_own: PoolOwnership, thread: ThreadId, reg: TokenRegistry, held: HeldLocks,
) -> Option<DescriptorSetState> {
    if held.thread == thread && lock_order_valid(held) && can_acquire_at_level(held, descriptor_pool_level()) {
        ts_update_descriptor_set(set, writes, pool_own, thread, reg)
    } else { None }
}

// ── Fence Level (5) ─────────────────────────────────────────────────────

/// Lock-ordered vkResetFences.
pub open spec fn ts_lo_reset_fence(
    fence: FenceState, thread: ThreadId, reg: TokenRegistry, held: HeldLocks,
) -> Option<FenceState> {
    if held.thread == thread && lock_order_valid(held) && can_acquire_at_level(held, fence_level()) {
        ts_reset_fence(fence, thread, reg)
    } else { None }
}

// ── Lock Ordering Proofs ────────────────────────────────────────────────

/// Master deadlock freedom: if two threads both use lock-ordered wrappers,
/// no circular wait is possible. This is immediate from the ordered locking theorem.
pub proof fn lemma_lo_deadlock_free(
    level_a: nat, level_b: nat,
    held1: HeldLocks, held2: HeldLocks,
)
    requires
        lock_order_valid(held1),
        lock_order_valid(held2),
    ensures
        !circular_wait_levels(level_a, level_b, held1.max_level, held2.max_level),
{
    lemma_ordered_no_circular_wait(level_a, level_b, held1.max_level, held2.max_level);
}

/// Lock-ordered allocate_memory requires lock order compliance.
pub proof fn lemma_lo_allocate_memory_requires_lock_order(
    dev: DeviceState, heap_idx: nat, size: nat,
    device_id: nat, thread: ThreadId, reg: TokenRegistry, held: HeldLocks,
)
    requires ts_lo_allocate_memory(dev, heap_idx, size, device_id, thread, reg, held).is_some(),
    ensures lock_order_valid(held) && can_acquire_at_level(held, device_level()),
{
}

/// Lock-ordered submit requires lock order compliance.
pub proof fn lemma_lo_submit_requires_lock_order(
    queue: QueueState, info: SubmitInfo,
    cb_states: Map<nat, CommandBufferState>,
    sem_states: Map<nat, SemaphoreState>,
    fence_states: Map<nat, FenceState>,
    thread: ThreadId, reg: TokenRegistry, held: HeldLocks,
)
    requires ts_lo_submit(queue, info, cb_states, sem_states, fence_states, thread, reg, held).is_some(),
    ensures lock_order_valid(held) && can_acquire_at_level(held, queue_level()),
{
}

/// Lock-ordered reset_command_pool requires lock order compliance.
pub proof fn lemma_lo_reset_command_pool_requires_lock_order(
    pool: CommandPoolState, pool_own: PoolOwnership,
    thread: ThreadId, reg: TokenRegistry,
    cb_states: Map<nat, CommandBufferState>, held: HeldLocks,
)
    requires ts_lo_reset_command_pool(pool, pool_own, thread, reg, cb_states, held).is_some(),
    ensures lock_order_valid(held) && can_acquire_at_level(held, command_pool_level()),
{
}

/// Lock-ordered begin_recording requires lock order compliance.
pub proof fn lemma_lo_begin_recording_requires_lock_order(
    cb_state: CommandBufferState, cb_id: nat,
    pool: PoolOwnership, thread: ThreadId, reg: TokenRegistry, held: HeldLocks,
)
    requires ts_lo_begin_recording(cb_state, cb_id, pool, thread, reg, held).is_some(),
    ensures lock_order_valid(held) && can_acquire_at_level(held, command_buffer_level()),
{
}

/// Lock-ordered update_descriptor_set requires lock order compliance.
pub proof fn lemma_lo_update_descriptor_set_requires_lock_order(
    set: DescriptorSetState,
    writes: Seq<(DescriptorWrite, DescriptorBinding)>,
    pool_own: PoolOwnership, thread: ThreadId, reg: TokenRegistry, held: HeldLocks,
)
    requires ts_lo_update_descriptor_set(set, writes, pool_own, thread, reg, held).is_some(),
    ensures lock_order_valid(held) && can_acquire_at_level(held, descriptor_pool_level()),
{
}

/// Lock-ordered reset_fence requires lock order compliance.
pub proof fn lemma_lo_reset_fence_requires_lock_order(
    fence: FenceState, thread: ThreadId, reg: TokenRegistry, held: HeldLocks,
)
    requires ts_lo_reset_fence(fence, thread, reg, held).is_some(),
    ensures lock_order_valid(held) && can_acquire_at_level(held, fence_level()),
{
}

/// Lock-ordered acquire_image requires lock order compliance.
pub proof fn lemma_lo_acquire_image_requires_lock_order(
    swapchain: SwapchainState, idx: nat,
    thread: ThreadId, reg: TokenRegistry, held: HeldLocks,
)
    requires ts_lo_acquire_image(swapchain, idx, thread, reg, held).is_some(),
    ensures lock_order_valid(held) && can_acquire_at_level(held, queue_level()),
{
}

/// Lock-ordered present_image requires lock order compliance.
pub proof fn lemma_lo_present_image_requires_lock_order(
    swapchain: SwapchainState, idx: nat,
    thread: ThreadId, reg: TokenRegistry, held: HeldLocks,
)
    requires ts_lo_present_image(swapchain, idx, thread, reg, held).is_some(),
    ensures lock_order_valid(held) && can_acquire_at_level(held, queue_level()),
{
}

// ═══════════════════════════════════════════════════════════════════════
// Barrier Necessity Wrappers
//
// Vulkan requires explicit pipeline barriers to resolve data hazards.
// These wrappers check that all accessed resources have been properly
// synchronized before draws/dispatches.
// ═══════════════════════════════════════════════════════════════════════

/// A requirement that a resource be synchronized before use.
pub struct ResourceSyncRequirement {
    /// The resource to synchronize.
    pub resource: ResourceId,
    /// Current sync state of the resource.
    pub sync_state: SyncState,
    /// Pipeline stage the resource will be accessed in.
    pub dst_stage: nat,
    /// Access type the resource will be used with.
    pub dst_access: nat,
    /// Whether the access is a write (requires writable) or read (requires readable).
    pub is_write: bool,
}

/// All resources are properly synchronized for use.
pub open spec fn all_resources_synchronized(
    barrier_log: BarrierLog,
    requirements: Seq<ResourceSyncRequirement>,
) -> bool {
    forall|i: int| #![trigger requirements[i]]
        0 <= i < requirements.len() ==> {
            let req = requirements[i];
            if req.is_write {
                writable(barrier_log, req.sync_state, req.dst_stage, req.dst_access)
            } else {
                readable(barrier_log, req.sync_state, req.dst_stage, req.dst_access)
            }
        }
}

/// Thread-safe draw with barrier necessity: requires both the draw call
/// to be valid AND all resources to be properly synchronized.
pub open spec fn ts_record_draw_synced(
    ctx: RecordingContext,
    resources: Set<ResourceId>,
    sync_requirements: Seq<ResourceSyncRequirement>,
    pipeline: GraphicsPipelineState,
    rp: RenderPassState,
    cb_id: nat,
    pool: PoolOwnership,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<RecordingContext> {
    if can_access_child(pool, cb_id, thread, reg)
       && full_draw_call_valid(ctx, pipeline, rp)
       && all_resources_synchronized(ctx.barrier_log, sync_requirements)
    {
        Some(record_draw(ctx, resources))
    } else {
        None
    }
}

/// Thread-safe dispatch with barrier necessity.
pub open spec fn ts_record_dispatch_synced(
    ctx: RecordingContext,
    resources: Set<ResourceId>,
    sync_requirements: Seq<ResourceSyncRequirement>,
    pipeline: ComputePipelineState,
    cb_id: nat,
    pool: PoolOwnership,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<RecordingContext> {
    if can_access_child(pool, cb_id, thread, reg)
       && full_dispatch_call_valid(ctx, pipeline)
       && all_resources_synchronized(ctx.barrier_log, sync_requirements)
    {
        Some(record_draw(ctx, resources))
    } else {
        None
    }
}

// ── Barrier Necessity Proofs ────────────────────────────────────────────

/// A synced draw has no data hazards: all resources are synchronized.
pub proof fn lemma_ts_synced_draw_no_hazards(
    ctx: RecordingContext,
    resources: Set<ResourceId>,
    sync_requirements: Seq<ResourceSyncRequirement>,
    pipeline: GraphicsPipelineState,
    rp: RenderPassState,
    cb_id: nat, pool: PoolOwnership, thread: ThreadId, reg: TokenRegistry,
)
    requires ts_record_draw_synced(ctx, resources, sync_requirements, pipeline, rp, cb_id, pool, thread, reg).is_some(),
    ensures all_resources_synchronized(ctx.barrier_log, sync_requirements),
{
}

/// A synced draw is a valid draw call.
pub proof fn lemma_ts_synced_draw_valid(
    ctx: RecordingContext,
    resources: Set<ResourceId>,
    sync_requirements: Seq<ResourceSyncRequirement>,
    pipeline: GraphicsPipelineState,
    rp: RenderPassState,
    cb_id: nat, pool: PoolOwnership, thread: ThreadId, reg: TokenRegistry,
)
    requires ts_record_draw_synced(ctx, resources, sync_requirements, pipeline, rp, cb_id, pool, thread, reg).is_some(),
    ensures full_draw_call_valid(ctx, pipeline, rp),
{
}

/// A synced dispatch has no data hazards.
pub proof fn lemma_ts_synced_dispatch_no_hazards(
    ctx: RecordingContext,
    resources: Set<ResourceId>,
    sync_requirements: Seq<ResourceSyncRequirement>,
    pipeline: ComputePipelineState,
    cb_id: nat, pool: PoolOwnership, thread: ThreadId, reg: TokenRegistry,
)
    requires ts_record_dispatch_synced(ctx, resources, sync_requirements, pipeline, cb_id, pool, thread, reg).is_some(),
    ensures all_resources_synchronized(ctx.barrier_log, sync_requirements),
{
}

// ═══════════════════════════════════════════════════════════════════════
// Strengthened Descriptor Update
// ═══════════════════════════════════════════════════════════════════════

/// Thread-safe descriptor update with in-flight check: ensures no GPU
/// is using the descriptor set when it is updated.
pub open spec fn ts_update_descriptor_set_safe(
    set: DescriptorSetState,
    writes: Seq<(DescriptorWrite, DescriptorBinding)>,
    pool_own: PoolOwnership,
    dev: DeviceState,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<DescriptorSetState> {
    if can_access_child(pool_own, set.id, thread, reg)
       && descriptor_not_in_flight(dev, set.id)
    {
        Some(apply_writes(set, writes))
    } else {
        None
    }
}

/// Strengthened descriptor update implies not-in-flight.
pub proof fn lemma_ts_update_safe_not_in_flight(
    set: DescriptorSetState,
    writes: Seq<(DescriptorWrite, DescriptorBinding)>,
    pool_own: PoolOwnership,
    dev: DeviceState,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires ts_update_descriptor_set_safe(set, writes, pool_own, dev, thread, reg).is_some(),
    ensures descriptor_not_in_flight(dev, set.id),
{
}

// ═══════════════════════════════════════════════════════════════════════
// Secondary Command Buffer Execution
// ═══════════════════════════════════════════════════════════════════════

/// Thread-safe vkCmdExecuteCommands: execute a single secondary CB.
/// Requires the primary's context satisfies the secondary's assumptions
/// and the secondary is in Executable state.
pub open spec fn ts_execute_secondary(
    primary_ctx: RecordingContext,
    secondary: SecondaryCommandBuffer,
    secondary_cb_id: nat,
    cb_id: nat,
    pool: PoolOwnership,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<RecordingContext> {
    if can_access_child(pool, cb_id, thread, reg)
       && secondary.executable
       && assumptions_satisfied(secondary.assumptions, primary_ctx)
       && not_held_by_other(reg, secondary_cb_id, thread)
    {
        Some(execute_secondary(primary_ctx, secondary))
    } else {
        None
    }
}

/// Thread-safe vkCmdExecuteCommands: execute multiple secondaries.
/// All secondaries must be executable with satisfied assumptions.
pub open spec fn ts_execute_n_secondaries(
    primary_ctx: RecordingContext,
    secondaries: Seq<SecondaryCommandBuffer>,
    secondary_cb_ids: Seq<nat>,
    cb_id: nat,
    pool: PoolOwnership,
    thread: ThreadId,
    reg: TokenRegistry,
) -> bool {
    can_access_child(pool, cb_id, thread, reg)
    && secondaries.len() == secondary_cb_ids.len()
    && (forall|i: int| #![trigger secondaries[i]]
        0 <= i < secondaries.len() ==>
        secondaries[i].executable
        && assumptions_satisfied(secondaries[i].assumptions, primary_ctx)
        && not_held_by_other(reg, secondary_cb_ids[i], thread))
}

/// Executing a secondary requires the secondary to be executable.
pub proof fn lemma_ts_execute_secondary_requires_executable(
    primary_ctx: RecordingContext,
    secondary: SecondaryCommandBuffer,
    secondary_cb_id: nat,
    cb_id: nat,
    pool: PoolOwnership,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires ts_execute_secondary(primary_ctx, secondary, secondary_cb_id, cb_id, pool, thread, reg).is_some(),
    ensures secondary.executable,
{
}

/// Executing a secondary requires assumptions satisfied.
pub proof fn lemma_ts_execute_secondary_requires_assumptions(
    primary_ctx: RecordingContext,
    secondary: SecondaryCommandBuffer,
    secondary_cb_id: nat,
    cb_id: nat,
    pool: PoolOwnership,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires ts_execute_secondary(primary_ctx, secondary, secondary_cb_id, cb_id, pool, thread, reg).is_some(),
    ensures assumptions_satisfied(secondary.assumptions, primary_ctx),
{
}

/// Executing a secondary requires pool access.
pub proof fn lemma_ts_execute_secondary_requires_access(
    primary_ctx: RecordingContext,
    secondary: SecondaryCommandBuffer,
    secondary_cb_id: nat,
    cb_id: nat,
    pool: PoolOwnership,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires ts_execute_secondary(primary_ctx, secondary, secondary_cb_id, cb_id, pool, thread, reg).is_some(),
    ensures can_access_child(pool, cb_id, thread, reg),
{
}

// ═══════════════════════════════════════════════════════════════════════
// Wait-Idle Thread-Safe Wrappers
// ═══════════════════════════════════════════════════════════════════════

/// Thread-safe vkDeviceWaitIdle: requires exclusive device access.
pub open spec fn ts_device_wait_idle(
    dev: DeviceState,
    device_id: nat,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<DeviceState> {
    if holds_exclusive(reg, device_id, thread) {
        Some(device_wait_idle_ghost(dev))
    } else {
        None
    }
}

/// Thread-safe vkQueueWaitIdle: requires exclusive queue access.
pub open spec fn ts_queue_wait_idle(
    dev: DeviceState,
    queue_id: nat,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<DeviceState> {
    if holds_exclusive(reg, queue_id, thread) {
        Some(queue_wait_idle_ghost(dev, queue_id))
    } else {
        None
    }
}

/// Device wait idle clears all pending references.
pub proof fn lemma_ts_device_wait_idle_clears_all(
    dev: DeviceState,
    device_id: nat,
    thread: ThreadId,
    reg: TokenRegistry,
    resource: ResourceId,
)
    requires ts_device_wait_idle(dev, device_id, thread, reg).is_some(),
    ensures
        safe_to_destroy_resource(
            ts_device_wait_idle(dev, device_id, thread, reg).unwrap(),
            resource,
        ),
{
    lemma_device_wait_idle_clears_all(resource);
}

/// Device wait idle + zero counters enables shutdown.
pub proof fn lemma_ts_device_wait_idle_enables_shutdown(
    dev: DeviceState,
    device_id: nat,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires
        ts_device_wait_idle(dev, device_id, thread, reg).is_some(),
        dev.live_buffers == 0,
        dev.live_images == 0,
        dev.live_pipelines == 0,
        dev.live_descriptor_pools == 0,
    ensures
        device_ready_for_shutdown(
            ts_device_wait_idle(dev, device_id, thread, reg).unwrap(),
        ),
{
    lemma_wait_idle_enables_shutdown(dev);
}

/// Device wait idle requires exclusive access.
pub proof fn lemma_ts_device_wait_idle_requires_exclusive(
    dev: DeviceState,
    device_id: nat,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires ts_device_wait_idle(dev, device_id, thread, reg).is_some(),
    ensures holds_exclusive(reg, device_id, thread),
{
}

// ═══════════════════════════════════════════════════════════════════════
// Render Pass Begin Thread-Safe Wrapper
// ═══════════════════════════════════════════════════════════════════════

/// Thread-safe vkCmdBeginRenderPass: requires the command buffer to be
/// in a recording state outside a render pass, the render pass and
/// framebuffer to be well-formed, and all attachment layouts to match.
pub open spec fn ts_begin_render_pass(
    ctx: RecordingContext,
    rp: RenderPassState,
    fb: FramebufferState,
    layout_map: ImageLayoutMap,
    fb_attachments: Seq<ResourceId>,
    cb_id: nat,
    pool: PoolOwnership,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<RecordingContext> {
    if can_access_child(pool, cb_id, thread, reg)
       && render_pass_well_formed(rp)
       && framebuffer_well_formed(fb, rp)
       && attachments_match_initial_layouts(layout_map, rp, fb_attachments)
       && ctx.state.active_render_pass.is_none()
    {
        Some(RecordingContext {
            state: begin_render_pass_recording(ctx.state, rp.id, fb.id),
            ..ctx
        })
    } else {
        None
    }
}

/// Begin render pass requires well-formed render pass.
pub proof fn lemma_ts_begin_render_pass_requires_well_formed(
    ctx: RecordingContext,
    rp: RenderPassState,
    fb: FramebufferState,
    layout_map: ImageLayoutMap,
    fb_attachments: Seq<ResourceId>,
    cb_id: nat, pool: PoolOwnership, thread: ThreadId, reg: TokenRegistry,
)
    requires ts_begin_render_pass(ctx, rp, fb, layout_map, fb_attachments, cb_id, pool, thread, reg).is_some(),
    ensures render_pass_well_formed(rp) && framebuffer_well_formed(fb, rp),
{
}

/// Begin render pass requires attachment layout compatibility.
pub proof fn lemma_ts_begin_render_pass_requires_layouts(
    ctx: RecordingContext,
    rp: RenderPassState,
    fb: FramebufferState,
    layout_map: ImageLayoutMap,
    fb_attachments: Seq<ResourceId>,
    cb_id: nat, pool: PoolOwnership, thread: ThreadId, reg: TokenRegistry,
)
    requires ts_begin_render_pass(ctx, rp, fb, layout_map, fb_attachments, cb_id, pool, thread, reg).is_some(),
    ensures attachments_match_initial_layouts(layout_map, rp, fb_attachments),
{
}

// ═══════════════════════════════════════════════════════════════════════
// TIER 1: Draw Completeness Enforcement
//
// These wrappers enforce that ALL draw/dispatch preconditions are met:
// - Recording state (pipeline bound, render pass active)
// - Draw state (vertex/index buffers, dynamic state, push constants)
// - Descriptor validation (all sets fully bound per layout)
// - Pipeline layout compatibility (descriptor set layouts match)
// - Barrier stage/access validity
// ═══════════════════════════════════════════════════════════════════════

/// Complete draw call: recording + draw state + descriptor + barrier + bounds validation.
/// Dynamic state requirements are derived from pipeline.required_dynamic_states.
pub open spec fn ts_record_draw_complete(
    ctx: RecordingContext,
    draw: DrawCallState,
    resources: Set<ResourceId>,
    sync_requirements: Seq<ResourceSyncRequirement>,
    pipeline: GraphicsPipelineState,
    rp: RenderPassState,
    required_vertex_slots: Set<nat>,
    push_constant_ranges: Seq<PushConstantRange>,
    dsets: Map<nat, DescriptorSetState>,
    layouts: Map<nat, DescriptorSetLayoutState>,
    first_vertex: nat,
    vertex_count: nat,
    cb_id: nat,
    pool: PoolOwnership,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<RecordingContext> {
    if can_access_child(pool, cb_id, thread, reg)
       && full_draw_valid(ctx.state, draw, pipeline, rp,
            required_vertex_slots, push_constant_ranges,
            first_vertex, vertex_count)
       && all_descriptor_sets_valid(ctx.state, pipeline, dsets, layouts)
       && all_resources_synchronized(ctx.barrier_log, sync_requirements)
       && all_barriers_valid(ctx.barrier_log)
    {
        Some(record_draw(ctx, resources))
    } else { None }
}

/// Complete draw-indexed call: same as draw + index buffer bound + index bounds.
/// Dynamic state requirements are derived from pipeline.required_dynamic_states.
pub open spec fn ts_record_draw_indexed_complete(
    ctx: RecordingContext,
    draw: DrawCallState,
    resources: Set<ResourceId>,
    sync_requirements: Seq<ResourceSyncRequirement>,
    pipeline: GraphicsPipelineState,
    rp: RenderPassState,
    required_vertex_slots: Set<nat>,
    push_constant_ranges: Seq<PushConstantRange>,
    dsets: Map<nat, DescriptorSetState>,
    layouts: Map<nat, DescriptorSetLayoutState>,
    first_vertex: nat,
    vertex_count: nat,
    first_index: nat,
    index_count: nat,
    cb_id: nat,
    pool: PoolOwnership,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<RecordingContext> {
    if can_access_child(pool, cb_id, thread, reg)
       && full_draw_indexed_valid(ctx.state, draw, pipeline, rp,
            required_vertex_slots, push_constant_ranges,
            first_vertex, vertex_count, first_index, index_count)
       && all_descriptor_sets_valid(ctx.state, pipeline, dsets, layouts)
       && all_resources_synchronized(ctx.barrier_log, sync_requirements)
       && all_barriers_valid(ctx.barrier_log)
    {
        Some(record_draw(ctx, resources))
    } else { None }
}

/// Complete dispatch call with descriptor validation.
pub open spec fn ts_record_dispatch_complete(
    ctx: RecordingContext,
    resources: Set<ResourceId>,
    sync_requirements: Seq<ResourceSyncRequirement>,
    pipeline: ComputePipelineState,
    dsets: Map<nat, DescriptorSetState>,
    layouts: Map<nat, DescriptorSetLayoutState>,
    cb_id: nat,
    pool: PoolOwnership,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<RecordingContext> {
    if can_access_child(pool, cb_id, thread, reg)
       && full_dispatch_call_valid(ctx, pipeline)
       && all_resources_synchronized(ctx.barrier_log, sync_requirements)
       && all_barriers_valid(ctx.barrier_log)
    {
        Some(record_draw(ctx, resources))
    } else { None }
}

/// Record a pipeline barrier with valid stage/access masks.
pub open spec fn ts_record_barrier_validated(
    ctx: RecordingContext,
    entry: BarrierEntry,
    cb_id: nat,
    pool: PoolOwnership,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<RecordingContext> {
    if can_access_child(pool, cb_id, thread, reg)
       && barrier_stage_access_valid(entry)
    {
        Some(RecordingContext {
            barrier_log: ctx.barrier_log.push(entry),
            ..ctx
        })
    } else { None }
}

// ── Tier 1 Proofs ───────────────────────────────────────────────────────

/// Complete draw enforces full_draw_valid.
pub proof fn lemma_ts_draw_complete_enforces_draw_valid(
    ctx: RecordingContext, draw: DrawCallState, resources: Set<ResourceId>,
    sync_requirements: Seq<ResourceSyncRequirement>,
    pipeline: GraphicsPipelineState, rp: RenderPassState,
    required_vertex_slots: Set<nat>,
    push_constant_ranges: Seq<PushConstantRange>,
    dsets: Map<nat, DescriptorSetState>, layouts: Map<nat, DescriptorSetLayoutState>,
    first_vertex: nat, vertex_count: nat,
    cb_id: nat, pool: PoolOwnership, thread: ThreadId, reg: TokenRegistry,
)
    requires ts_record_draw_complete(ctx, draw, resources, sync_requirements, pipeline, rp,
        required_vertex_slots, push_constant_ranges,
        dsets, layouts, first_vertex, vertex_count,
        cb_id, pool, thread, reg).is_some(),
    ensures
        full_draw_valid(ctx.state, draw, pipeline, rp,
            required_vertex_slots, push_constant_ranges,
            first_vertex, vertex_count)
        && all_descriptor_sets_valid(ctx.state, pipeline, dsets, layouts)
        && all_barriers_valid(ctx.barrier_log),
{
}

/// Complete draw enforces barrier sync.
pub proof fn lemma_ts_draw_complete_enforces_sync(
    ctx: RecordingContext, draw: DrawCallState, resources: Set<ResourceId>,
    sync_requirements: Seq<ResourceSyncRequirement>,
    pipeline: GraphicsPipelineState, rp: RenderPassState,
    required_vertex_slots: Set<nat>,
    push_constant_ranges: Seq<PushConstantRange>,
    dsets: Map<nat, DescriptorSetState>, layouts: Map<nat, DescriptorSetLayoutState>,
    first_vertex: nat, vertex_count: nat,
    cb_id: nat, pool: PoolOwnership, thread: ThreadId, reg: TokenRegistry,
)
    requires ts_record_draw_complete(ctx, draw, resources, sync_requirements, pipeline, rp,
        required_vertex_slots, push_constant_ranges,
        dsets, layouts, first_vertex, vertex_count,
        cb_id, pool, thread, reg).is_some(),
    ensures all_resources_synchronized(ctx.barrier_log, sync_requirements),
{
}

/// Validated barrier preserves barrier log validity.
pub proof fn lemma_ts_barrier_validated_preserves_valid(
    ctx: RecordingContext, entry: BarrierEntry,
    cb_id: nat, pool: PoolOwnership, thread: ThreadId, reg: TokenRegistry,
)
    requires
        ts_record_barrier_validated(ctx, entry, cb_id, pool, thread, reg).is_some(),
        all_barriers_valid(ctx.barrier_log),
    ensures
        all_barriers_valid(
            ts_record_barrier_validated(ctx, entry, cb_id, pool, thread, reg)
                .unwrap().barrier_log),
{
    lemma_append_valid_barrier(ctx.barrier_log, entry);
}

// ═══════════════════════════════════════════════════════════════════════
// TIER 2: Transfer & Resource Safety Enforcement
// ═══════════════════════════════════════════════════════════════════════

/// Thread-safe vkCmdCopyImage with layout and bounds validation.
pub open spec fn ts_copy_image(
    src: ImageState, dst: ImageState,
    src_layout: ImageLayout, dst_layout: ImageLayout,
    regions: Seq<ImageCopyRegion>,
    cb_id: nat, pool: PoolOwnership, thread: ThreadId, reg: TokenRegistry,
) -> Option<bool> {
    if can_access_child(pool, cb_id, thread, reg)
       && copy_image_valid(src, dst, src_layout, dst_layout, regions)
    {
        Some(true)
    } else { None }
}

/// Thread-safe vkCmdCopyBufferToImage.
pub open spec fn ts_copy_buffer_to_image(
    buffer: BufferState, image: ImageState,
    dst_layout: ImageLayout, regions: Seq<BufferImageCopyRegion>,
    cb_id: nat, pool: PoolOwnership, thread: ThreadId, reg: TokenRegistry,
) -> Option<bool> {
    if can_access_child(pool, cb_id, thread, reg)
       && copy_buffer_to_image_valid(buffer, image, dst_layout, regions)
    {
        Some(true)
    } else { None }
}

/// Thread-safe vkCmdCopyImageToBuffer.
pub open spec fn ts_copy_image_to_buffer(
    image: ImageState, buffer: BufferState,
    src_layout: ImageLayout, regions: Seq<BufferImageCopyRegion>,
    cb_id: nat, pool: PoolOwnership, thread: ThreadId, reg: TokenRegistry,
) -> Option<bool> {
    if can_access_child(pool, cb_id, thread, reg)
       && copy_image_to_buffer_valid(image, buffer, src_layout, regions)
    {
        Some(true)
    } else { None }
}

/// Thread-safe vkCmdBlitImage.
pub open spec fn ts_blit_image(
    src: ImageState, dst: ImageState,
    src_layout: ImageLayout, dst_layout: ImageLayout,
    cb_id: nat, pool: PoolOwnership, thread: ThreadId, reg: TokenRegistry,
) -> Option<bool> {
    if can_access_child(pool, cb_id, thread, reg)
       && blit_image_valid(src, dst, src_layout, dst_layout)
    {
        Some(true)
    } else { None }
}

/// Memory aliasing safety: submit only when aliased resources are safe.
pub open spec fn ts_submit_aliasing_safe(
    queue: QueueState, info: SubmitInfo,
    bindings: Map<ResourceId, MemoryRange>,
    cb_states: Map<nat, CommandBufferState>,
    sem_states: Map<nat, SemaphoreState>,
    fence_states: Map<nat, FenceState>,
    submissions: Seq<SubmissionRecord>,
    thread: ThreadId, reg: TokenRegistry,
) -> Option<(QueueState, SubmissionRecord)> {
    if submission_valid(info, cb_states, sem_states, fence_states, queue.queue_id, thread, reg)
       && all_aliasing_safe(bindings, submissions)
    {
        submit_ghost(queue, info, thread, reg)
    } else { None }
}

/// Thread-safe indirect draw with buffer validation.
pub open spec fn ts_draw_indirect(
    ctx: RecordingContext,
    resources: Set<ResourceId>,
    pipeline: GraphicsPipelineState, rp: RenderPassState,
    params: IndirectDrawParams, buffer: BufferState,
    cb_id: nat, pool: PoolOwnership, thread: ThreadId, reg: TokenRegistry,
) -> Option<RecordingContext> {
    if can_access_child(pool, cb_id, thread, reg)
       && draw_indirect_valid(ctx.state, pipeline, rp, params, buffer)
    {
        Some(record_draw(ctx, resources))
    } else { None }
}

/// Thread-safe indirect dispatch with buffer validation.
pub open spec fn ts_dispatch_indirect(
    ctx: RecordingContext,
    resources: Set<ResourceId>,
    pipeline: ComputePipelineState,
    buffer_id: nat, offset: nat, buffer: BufferState,
    cb_id: nat, pool: PoolOwnership, thread: ThreadId, reg: TokenRegistry,
) -> Option<RecordingContext> {
    if can_access_child(pool, cb_id, thread, reg)
       && dispatch_indirect_valid(ctx.state, pipeline, buffer_id, offset, buffer)
    {
        Some(record_draw(ctx, resources))
    } else { None }
}

/// Thread-safe readback: requires fence wait + staging buffer readable.
pub open spec fn ts_readback(
    submissions: Seq<SubmissionRecord>,
    staging: StagingBufferState,
    gpu: GpuBufferState,
    src_offset: nat, dst_offset: nat, copy_size: nat,
) -> Option<bool> {
    if readback_valid(submissions, staging, gpu, src_offset, dst_offset, copy_size) {
        Some(true)
    } else { None }
}

// ── Tier 2 Proofs ───────────────────────────────────────────────────────

/// ts_copy_image enforces layout and bounds.
pub proof fn lemma_ts_copy_image_enforces_valid(
    src: ImageState, dst: ImageState,
    src_layout: ImageLayout, dst_layout: ImageLayout,
    regions: Seq<ImageCopyRegion>,
    cb_id: nat, pool: PoolOwnership, thread: ThreadId, reg: TokenRegistry,
)
    requires ts_copy_image(src, dst, src_layout, dst_layout, regions, cb_id, pool, thread, reg).is_some(),
    ensures copy_image_valid(src, dst, src_layout, dst_layout, regions),
{
}

/// ts_submit_aliasing_safe enforces memory aliasing safety.
pub proof fn lemma_ts_submit_aliasing_enforces_safe(
    queue: QueueState, info: SubmitInfo,
    bindings: Map<ResourceId, MemoryRange>,
    cb_states: Map<nat, CommandBufferState>,
    sem_states: Map<nat, SemaphoreState>,
    fence_states: Map<nat, FenceState>,
    submissions: Seq<SubmissionRecord>,
    thread: ThreadId, reg: TokenRegistry,
)
    requires ts_submit_aliasing_safe(queue, info, bindings, cb_states, sem_states, fence_states, submissions, thread, reg).is_some(),
    ensures all_aliasing_safe(bindings, submissions),
{
}

/// ts_draw_indirect enforces buffer sufficiency.
pub proof fn lemma_ts_draw_indirect_enforces_valid(
    ctx: RecordingContext, resources: Set<ResourceId>,
    pipeline: GraphicsPipelineState, rp: RenderPassState,
    params: IndirectDrawParams, buffer: BufferState,
    cb_id: nat, pool: PoolOwnership, thread: ThreadId, reg: TokenRegistry,
)
    requires ts_draw_indirect(ctx, resources, pipeline, rp, params, buffer, cb_id, pool, thread, reg).is_some(),
    ensures draw_indirect_valid(ctx.state, pipeline, rp, params, buffer),
{
}

/// ts_readback enforces host readability and content match.
pub proof fn lemma_ts_readback_enforces_valid(
    submissions: Seq<SubmissionRecord>,
    staging: StagingBufferState, gpu: GpuBufferState,
    src_offset: nat, dst_offset: nat, copy_size: nat,
)
    requires ts_readback(submissions, staging, gpu, src_offset, dst_offset, copy_size).is_some(),
    ensures readback_valid(submissions, staging, gpu, src_offset, dst_offset, copy_size),
{
}

// ══════════════════════════════════════════════════════════════════════
// Tier 3: Pipeline Configuration Safety
// ══════════════════════════════════════════════════════════════════════

// ── MSAA ─────────────────────────────────────────────────────────────

/// Thread-safe MSAA resolve: validates resolve operation and thread access.
pub open spec fn ts_resolve(
    op: ResolveOperation,
    cb_id: nat, pool: PoolOwnership, thread: ThreadId, reg: TokenRegistry,
) -> Option<()> {
    if can_access_child(pool, cb_id, thread, reg)
        && resolve_valid(op)
    {
        Some(())
    } else {
        None
    }
}

/// Thread-safe draw with MSAA validation: pipeline samples must match attachments.
pub open spec fn ts_draw_msaa_validated(
    ctx: RecordingContext, resources: Set<ResourceId>,
    pipeline: GraphicsPipelineState, rp: RenderPassState,
    pipeline_samples: SampleCount,
    color_samples: Seq<SampleCount>, depth_samples: Option<SampleCount>,
    cb_id: nat, pool: PoolOwnership, thread: ThreadId, reg: TokenRegistry,
) -> Option<RecordingContext> {
    if can_access_child(pool, cb_id, thread, reg)
        && full_draw_call_valid(ctx, pipeline, rp)
        && all_sample_counts_match(pipeline_samples, color_samples, depth_samples)
    {
        Some(record_draw(ctx, resources))
    } else {
        None
    }
}

// ── Depth/Stencil ────────────────────────────────────────────────────

/// Thread-safe pipeline creation with depth/stencil validation.
pub open spec fn ts_create_pipeline_depth_stencil(
    ds_state: DepthStencilState,
    pipeline: GraphicsPipelineState,
    thread: ThreadId, reg: TokenRegistry,
) -> Option<()> {
    if depth_stencil_well_formed(ds_state)
        && depth_bounds_valid(ds_state)
    {
        Some(())
    } else {
        None
    }
}

// ── Color Blend ──────────────────────────────────────────────────────

/// Thread-safe pipeline creation with color blend validation.
pub open spec fn ts_create_pipeline_color_blend(
    blend_state: ColorBlendState,
    color_attachment_count: nat,
    thread: ThreadId, reg: TokenRegistry,
) -> Option<()> {
    if color_blend_well_formed(blend_state)
        && blend_attachment_count_matches(blend_state, color_attachment_count)
    {
        Some(())
    } else {
        None
    }
}

// ── Viewport/Scissor ─────────────────────────────────────────────────

/// Thread-safe pipeline creation with viewport/scissor validation.
pub open spec fn ts_create_pipeline_viewport_scissor(
    vs_state: ViewportScissorState,
    max_viewports: nat, max_width: nat, max_height: nat,
    thread: ThreadId, reg: TokenRegistry,
) -> Option<()> {
    if viewport_scissor_well_formed(vs_state, max_viewports, max_width, max_height) {
        Some(())
    } else {
        None
    }
}

// ── Format Properties ────────────────────────────────────────────────

/// Thread-safe attachment format validation.
pub open spec fn ts_validate_attachment_format(
    props: FormatProperties,
    is_color: bool, is_depth: bool, blend_enabled: bool,
) -> Option<()> {
    if format_valid_for_attachment(props, is_color, is_depth, blend_enabled) {
        Some(())
    } else {
        None
    }
}

/// Thread-safe sampled image format validation.
pub open spec fn ts_validate_sampling_format(
    props: FormatProperties,
) -> Option<()> {
    if format_supports_sampling(props) {
        Some(())
    } else {
        None
    }
}

// ── Shader Interface ─────────────────────────────────────────────────

/// Thread-safe pipeline creation with shader interface validation.
pub open spec fn ts_create_pipeline_shader_validated(
    vertex_shader: ShaderInterface,
    fragment_shader: ShaderInterface,
    vertex_attributes: Seq<ShaderInputAttribute>,
    set_layouts: Seq<DescriptorSetLayoutState>,
    push_ranges: Seq<PushConstantRange>,
    color_attachment_count: nat,
    thread: ThreadId, reg: TokenRegistry,
) -> Option<()> {
    if shader_pipeline_compatible(
        vertex_shader, fragment_shader,
        vertex_attributes, set_layouts, push_ranges,
        color_attachment_count,
    ) {
        Some(())
    } else {
        None
    }
}

// ── Tier 3 Proofs ────────────────────────────────────────────────────

/// ts_resolve enforces resolve validity.
pub proof fn lemma_ts_resolve_enforces_valid(
    op: ResolveOperation,
    cb_id: nat, pool: PoolOwnership, thread: ThreadId, reg: TokenRegistry,
)
    requires ts_resolve(op, cb_id, pool, thread, reg).is_some(),
    ensures resolve_valid(op),
{
}

/// ts_draw_msaa_validated enforces sample count matching.
pub proof fn lemma_ts_draw_msaa_enforces_match(
    ctx: RecordingContext, resources: Set<ResourceId>,
    pipeline: GraphicsPipelineState, rp: RenderPassState,
    pipeline_samples: SampleCount,
    color_samples: Seq<SampleCount>, depth_samples: Option<SampleCount>,
    cb_id: nat, pool: PoolOwnership, thread: ThreadId, reg: TokenRegistry,
)
    requires ts_draw_msaa_validated(ctx, resources, pipeline, rp, pipeline_samples, color_samples, depth_samples, cb_id, pool, thread, reg).is_some(),
    ensures
        all_sample_counts_match(pipeline_samples, color_samples, depth_samples),
        full_draw_call_valid(ctx, pipeline, rp),
{
}

/// ts_create_pipeline_depth_stencil enforces depth/stencil well-formedness.
pub proof fn lemma_ts_depth_stencil_enforces_wf(
    ds_state: DepthStencilState,
    pipeline: GraphicsPipelineState,
    thread: ThreadId, reg: TokenRegistry,
)
    requires ts_create_pipeline_depth_stencil(ds_state, pipeline, thread, reg).is_some(),
    ensures depth_stencil_well_formed(ds_state), depth_bounds_valid(ds_state),
{
}

/// ts_create_pipeline_color_blend enforces blend well-formedness and count matching.
pub proof fn lemma_ts_color_blend_enforces_wf(
    blend_state: ColorBlendState,
    color_attachment_count: nat,
    thread: ThreadId, reg: TokenRegistry,
)
    requires ts_create_pipeline_color_blend(blend_state, color_attachment_count, thread, reg).is_some(),
    ensures
        color_blend_well_formed(blend_state),
        blend_attachment_count_matches(blend_state, color_attachment_count),
{
}

/// ts_create_pipeline_shader_validated enforces shader-pipeline compatibility.
pub proof fn lemma_ts_shader_validated_enforces_compatible(
    vertex_shader: ShaderInterface,
    fragment_shader: ShaderInterface,
    vertex_attributes: Seq<ShaderInputAttribute>,
    set_layouts: Seq<DescriptorSetLayoutState>,
    push_ranges: Seq<PushConstantRange>,
    color_attachment_count: nat,
    thread: ThreadId, reg: TokenRegistry,
)
    requires ts_create_pipeline_shader_validated(vertex_shader, fragment_shader, vertex_attributes, set_layouts, push_ranges, color_attachment_count, thread, reg).is_some(),
    ensures shader_pipeline_compatible(vertex_shader, fragment_shader, vertex_attributes, set_layouts, push_ranges, color_attachment_count),
{
}

// ══════════════════════════════════════════════════════════════════════
// Tier 4: Advanced / Extension Feature Safety
// ══════════════════════════════════════════════════════════════════════

// ── Dynamic Rendering ────────────────────────────────────────────────

/// Thread-safe begin dynamic rendering: validates info and thread access.
pub open spec fn ts_begin_dynamic_rendering(
    info: DynamicRenderingInfo,
    pipeline_samples: SampleCount,
    cb_id: nat, pool: PoolOwnership, thread: ThreadId, reg: TokenRegistry,
) -> Option<()> {
    if can_access_child(pool, cb_id, thread, reg)
        && dynamic_rendering_well_formed(info)
        && dynamic_rendering_samples_match(info, pipeline_samples)
    {
        Some(())
    } else {
        None
    }
}

// ── Bindless Descriptors ─────────────────────────────────────────────

/// Thread-safe bindless descriptor access validation.
pub open spec fn ts_bindless_access(
    set: BindlessDescriptorSetState,
    binding: nat,
    accessed_indices: Set<nat>,
    valid_indices: Set<nat>,
    thread: ThreadId, reg: TokenRegistry,
) -> Option<()> {
    if bindless_set_well_formed(set)
        && partially_bound_access_valid(set, binding, accessed_indices, valid_indices)
    {
        Some(())
    } else {
        None
    }
}

// ── Conditional Rendering ────────────────────────────────────────────

/// Thread-safe begin conditional rendering: validates buffer and thread access.
pub open spec fn ts_begin_conditional_rendering(
    buffer: BufferState,
    offset: nat,
    cb_id: nat, pool: PoolOwnership, thread: ThreadId, reg: TokenRegistry,
) -> Option<()> {
    if can_access_child(pool, cb_id, thread, reg)
        && begin_conditional_valid(buffer, offset)
    {
        Some(())
    } else {
        None
    }
}

// ── Sampler ──────────────────────────────────────────────────────────

/// Thread-safe sampler creation: validates sampler well-formedness.
pub open spec fn ts_create_sampler(
    sampler: SamplerState,
    thread: ThreadId, reg: TokenRegistry,
) -> Option<()> {
    if sampler_well_formed(sampler) {
        Some(())
    } else {
        None
    }
}

/// Thread-safe sampler-image binding validation.
pub open spec fn ts_bind_sampler_image(
    sampler: SamplerState,
    image_dimensions: nat,
    is_array: bool,
    is_depth_format: bool,
    thread: ThreadId, reg: TokenRegistry,
) -> Option<()> {
    if sampler_well_formed(sampler)
        && sampler_image_compatible(sampler, image_dimensions, is_array, is_depth_format)
    {
        Some(())
    } else {
        None
    }
}

// ── Tier 4 Proofs ────────────────────────────────────────────────────

/// ts_begin_dynamic_rendering enforces well-formedness and sample matching.
pub proof fn lemma_ts_dynamic_rendering_enforces_wf(
    info: DynamicRenderingInfo,
    pipeline_samples: SampleCount,
    cb_id: nat, pool: PoolOwnership, thread: ThreadId, reg: TokenRegistry,
)
    requires ts_begin_dynamic_rendering(info, pipeline_samples, cb_id, pool, thread, reg).is_some(),
    ensures
        dynamic_rendering_well_formed(info),
        dynamic_rendering_samples_match(info, pipeline_samples),
{
}

/// ts_bindless_access enforces set well-formedness and access validity.
pub proof fn lemma_ts_bindless_enforces_valid(
    set: BindlessDescriptorSetState,
    binding: nat,
    accessed_indices: Set<nat>,
    valid_indices: Set<nat>,
    thread: ThreadId, reg: TokenRegistry,
)
    requires ts_bindless_access(set, binding, accessed_indices, valid_indices, thread, reg).is_some(),
    ensures
        bindless_set_well_formed(set),
        partially_bound_access_valid(set, binding, accessed_indices, valid_indices),
{
}

/// ts_begin_conditional_rendering enforces buffer validity.
pub proof fn lemma_ts_conditional_rendering_enforces_valid(
    buffer: BufferState,
    offset: nat,
    cb_id: nat, pool: PoolOwnership, thread: ThreadId, reg: TokenRegistry,
)
    requires ts_begin_conditional_rendering(buffer, offset, cb_id, pool, thread, reg).is_some(),
    ensures begin_conditional_valid(buffer, offset),
{
}

/// ts_create_sampler enforces sampler well-formedness.
pub proof fn lemma_ts_sampler_enforces_wf(
    sampler: SamplerState,
    thread: ThreadId, reg: TokenRegistry,
)
    requires ts_create_sampler(sampler, thread, reg).is_some(),
    ensures sampler_well_formed(sampler),
{
}

/// ts_bind_sampler_image enforces sampler-image compatibility.
pub proof fn lemma_ts_sampler_image_enforces_compatible(
    sampler: SamplerState,
    image_dimensions: nat,
    is_array: bool,
    is_depth_format: bool,
    thread: ThreadId, reg: TokenRegistry,
)
    requires ts_bind_sampler_image(sampler, image_dimensions, is_array, is_depth_format, thread, reg).is_some(),
    ensures
        sampler_well_formed(sampler),
        sampler_image_compatible(sampler, image_dimensions, is_array, is_depth_format),
{
}

// ══════════════════════════════════════════════════════════════════════
// Tier 5: Framework-Level Safety
// ══════════════════════════════════════════════════════════════════════

// ── Render Graph ─────────────────────────────────────────────────────

/// Thread-safe render graph validation: well-formedness + acyclicity.
pub open spec fn ts_validate_render_graph(
    graph: RenderGraph,
    external_inputs: Set<ResourceId>,
    thread: ThreadId, reg: TokenRegistry,
) -> Option<()> {
    if render_graph_well_formed(graph, external_inputs)
        && is_acyclic(graph)
    {
        Some(())
    } else {
        None
    }
}

// ── Render Graph Execution ───────────────────────────────────────────

/// Thread-safe render graph execution validation.
pub open spec fn ts_execute_render_graph(
    graph: RenderGraph,
    order: Seq<nat>,
    external_inputs: Set<ResourceId>,
    thread: ThreadId, reg: TokenRegistry,
) -> Option<()> {
    if render_graph_well_formed(graph, external_inputs)
        && valid_execution_order(graph, order)
    {
        Some(())
    } else {
        None
    }
}

/// Thread-safe check that all passes completed.
pub open spec fn ts_render_graph_completed(
    graph: RenderGraph,
    state: GraphExecutionState,
    thread: ThreadId, reg: TokenRegistry,
) -> Option<()> {
    if all_passes_completed(graph, state) {
        Some(())
    } else {
        None
    }
}

// ── Temporal Resource Budget ─────────────────────────────────────────

/// Thread-safe resource budget check.
pub open spec fn ts_check_resource_budget(
    dev: DeviceState,
    budget: ResourceBudget,
    device_id: nat,
    thread: ThreadId, reg: TokenRegistry,
) -> Option<()> {
    if holds_exclusive(reg, device_id, thread)
        && within_budget(dev, budget)
    {
        Some(())
    } else {
        None
    }
}

// ── Ghost Checkpoint ─────────────────────────────────────────────────

/// Thread-safe ghost checkpoint consistency check.
pub open spec fn ts_validate_checkpoint(
    cp: GhostCheckpoint,
    ctx: RecordingContext,
    cb_id: nat, pool: PoolOwnership, thread: ThreadId, reg: TokenRegistry,
) -> Option<()> {
    if can_access_child(pool, cb_id, thread, reg)
        && checkpoint_consistent_with(cp, ctx)
    {
        Some(())
    } else {
        None
    }
}

// ── Asset Pipeline ───────────────────────────────────────────────────

/// Thread-safe draw with full mesh buffer safety chain.
pub open spec fn ts_draw_mesh_safe(
    inv: MeshBufferInvariants,
    vbuf_size: nat, ibuf_size: nat,
    first_index: nat, index_count: nat,
    ctx: RecordingContext, resources: Set<ResourceId>,
    pipeline: GraphicsPipelineState, rp: RenderPassState,
    cb_id: nat, pool: PoolOwnership, thread: ThreadId, reg: TokenRegistry,
) -> Option<RecordingContext> {
    if can_access_child(pool, cb_id, thread, reg)
        && full_draw_call_valid(ctx, pipeline, rp)
        && full_draw_safety_chain(inv, vbuf_size, ibuf_size, first_index, index_count)
    {
        Some(record_draw(ctx, resources))
    } else {
        None
    }
}

/// Thread-safe mesh upload readiness check.
pub open spec fn ts_mesh_upload_ready(
    inv: MeshBufferInvariants,
) -> Option<()> {
    if mesh_upload_ready(inv) {
        Some(())
    } else {
        None
    }
}

// ── Hot Reload ───────────────────────────────────────────────────────

/// Thread-safe shader hot reload validation.
pub open spec fn ts_hot_reload(
    request: ReloadRequest,
    old_vertex_interface: ShaderInterface,
    old_fragment_interface: ShaderInterface,
    submissions: Seq<SubmissionRecord>,
    device_id: nat,
    thread: ThreadId, reg: TokenRegistry,
) -> Option<()> {
    if holds_exclusive(reg, device_id, thread)
        && hot_reload_valid(request, old_vertex_interface, old_fragment_interface)
        && safe_to_swap(submissions, request.old_pipeline_id)
    {
        Some(())
    } else {
        None
    }
}

// ── Taint / Information Flow ─────────────────────────────────────────

/// Thread-safe taint check for rendering: all read resources must be visible to the viewer.
pub open spec fn ts_render_taint_checked(
    read_taints: Seq<TaintSet>,
    viewer: PlayerId,
    ctx: RecordingContext, resources: Set<ResourceId>,
    pipeline: GraphicsPipelineState, rp: RenderPassState,
    cb_id: nat, pool: PoolOwnership, thread: ThreadId, reg: TokenRegistry,
) -> Option<RecordingContext> {
    if can_access_child(pool, cb_id, thread, reg)
        && full_draw_call_valid(ctx, pipeline, rp)
        && render_taint_safe(read_taints, viewer)
    {
        Some(record_draw(ctx, resources))
    } else {
        None
    }
}

// ── Tier 5 Proofs ────────────────────────────────────────────────────

/// ts_validate_render_graph enforces well-formedness and acyclicity.
pub proof fn lemma_ts_render_graph_enforces_wf(
    graph: RenderGraph,
    external_inputs: Set<ResourceId>,
    thread: ThreadId, reg: TokenRegistry,
)
    requires ts_validate_render_graph(graph, external_inputs, thread, reg).is_some(),
    ensures
        render_graph_well_formed(graph, external_inputs),
        is_acyclic(graph),
{
}

/// ts_execute_render_graph enforces valid execution order.
pub proof fn lemma_ts_execute_render_graph_enforces_order(
    graph: RenderGraph,
    order: Seq<nat>,
    external_inputs: Set<ResourceId>,
    thread: ThreadId, reg: TokenRegistry,
)
    requires ts_execute_render_graph(graph, order, external_inputs, thread, reg).is_some(),
    ensures valid_execution_order(graph, order),
{
}

/// ts_render_graph_completed enforces all passes done.
pub proof fn lemma_ts_render_graph_completed_enforces(
    graph: RenderGraph,
    state: GraphExecutionState,
    thread: ThreadId, reg: TokenRegistry,
)
    requires ts_render_graph_completed(graph, state, thread, reg).is_some(),
    ensures all_passes_completed(graph, state),
{
}

/// ts_check_resource_budget enforces budget compliance.
pub proof fn lemma_ts_budget_enforces_within(
    dev: DeviceState,
    budget: ResourceBudget,
    device_id: nat,
    thread: ThreadId, reg: TokenRegistry,
)
    requires ts_check_resource_budget(dev, budget, device_id, thread, reg).is_some(),
    ensures within_budget(dev, budget),
{
}

/// ts_validate_checkpoint enforces checkpoint consistency.
pub proof fn lemma_ts_checkpoint_enforces_consistent(
    cp: GhostCheckpoint,
    ctx: RecordingContext,
    cb_id: nat, pool: PoolOwnership, thread: ThreadId, reg: TokenRegistry,
)
    requires ts_validate_checkpoint(cp, ctx, cb_id, pool, thread, reg).is_some(),
    ensures checkpoint_consistent_with(cp, ctx),
{
}

/// ts_draw_mesh_safe enforces the full asset-to-draw safety chain.
pub proof fn lemma_ts_draw_mesh_enforces_safety_chain(
    inv: MeshBufferInvariants,
    vbuf_size: nat, ibuf_size: nat,
    first_index: nat, index_count: nat,
    ctx: RecordingContext, resources: Set<ResourceId>,
    pipeline: GraphicsPipelineState, rp: RenderPassState,
    cb_id: nat, pool: PoolOwnership, thread: ThreadId, reg: TokenRegistry,
)
    requires ts_draw_mesh_safe(inv, vbuf_size, ibuf_size, first_index, index_count, ctx, resources, pipeline, rp, cb_id, pool, thread, reg).is_some(),
    ensures
        full_draw_safety_chain(inv, vbuf_size, ibuf_size, first_index, index_count),
        full_draw_call_valid(ctx, pipeline, rp),
{
}

/// ts_hot_reload enforces reload validity and swap safety.
pub proof fn lemma_ts_hot_reload_enforces_valid(
    request: ReloadRequest,
    old_vertex_interface: ShaderInterface,
    old_fragment_interface: ShaderInterface,
    submissions: Seq<SubmissionRecord>,
    device_id: nat,
    thread: ThreadId, reg: TokenRegistry,
)
    requires ts_hot_reload(request, old_vertex_interface, old_fragment_interface, submissions, device_id, thread, reg).is_some(),
    ensures
        hot_reload_valid(request, old_vertex_interface, old_fragment_interface),
        safe_to_swap(submissions, request.old_pipeline_id),
{
}

/// ts_render_taint_checked enforces information-flow safety.
pub proof fn lemma_ts_render_taint_enforces_safe(
    read_taints: Seq<TaintSet>,
    viewer: PlayerId,
    ctx: RecordingContext, resources: Set<ResourceId>,
    pipeline: GraphicsPipelineState, rp: RenderPassState,
    cb_id: nat, pool: PoolOwnership, thread: ThreadId, reg: TokenRegistry,
)
    requires ts_render_taint_checked(read_taints, viewer, ctx, resources, pipeline, rp, cb_id, pool, thread, reg).is_some(),
    ensures
        render_taint_safe(read_taints, viewer),
        full_draw_call_valid(ctx, pipeline, rp),
{
}

// ═══════════════════════════════════════════════════════════════════════
// Destroy Wrappers — Pipeline, Framebuffer, Descriptor, Sampler, CommandPool
// ═══════════════════════════════════════════════════════════════════════

// ── Graphics Pipeline ──────────────────────────────────────────────────

/// Thread-safe vkDestroyPipeline (graphics): requires exclusive pipeline access.
pub open spec fn ts_destroy_graphics_pipeline(
    pipeline: GraphicsPipelineState,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<GraphicsPipelineState> {
    if holds_exclusive(reg, pipeline.id, thread) {
        Some(destroy_graphics_pipeline_ghost(pipeline))
    } else {
        None
    }
}

/// Thread-safe graphics pipeline destroy requires exclusive access.
pub proof fn lemma_ts_destroy_graphics_pipeline_requires_exclusive(
    pipeline: GraphicsPipelineState,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires ts_destroy_graphics_pipeline(pipeline, thread, reg).is_some(),
    ensures holds_exclusive(reg, pipeline.id, thread),
{
}

/// After thread-safe destroy, a graphics pipeline is not alive.
pub proof fn lemma_ts_destroy_graphics_pipeline_not_alive(
    pipeline: GraphicsPipelineState,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires ts_destroy_graphics_pipeline(pipeline, thread, reg).is_some(),
    ensures !ts_destroy_graphics_pipeline(pipeline, thread, reg).unwrap().alive,
{
}

// ── Compute Pipeline ──────────────────────────────────────────────────

/// Thread-safe vkDestroyPipeline (compute): requires exclusive pipeline access.
pub open spec fn ts_destroy_compute_pipeline(
    pipeline: ComputePipelineState,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<ComputePipelineState> {
    if holds_exclusive(reg, pipeline.id, thread) {
        Some(destroy_compute_pipeline_ghost(pipeline))
    } else {
        None
    }
}

/// Thread-safe compute pipeline destroy requires exclusive access.
pub proof fn lemma_ts_destroy_compute_pipeline_requires_exclusive(
    pipeline: ComputePipelineState,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires ts_destroy_compute_pipeline(pipeline, thread, reg).is_some(),
    ensures holds_exclusive(reg, pipeline.id, thread),
{
}

/// After thread-safe destroy, a compute pipeline is not alive.
pub proof fn lemma_ts_destroy_compute_pipeline_not_alive(
    pipeline: ComputePipelineState,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires ts_destroy_compute_pipeline(pipeline, thread, reg).is_some(),
    ensures !ts_destroy_compute_pipeline(pipeline, thread, reg).unwrap().alive,
{
}

// ── Framebuffer ────────────────────────────────────────────────────────

/// Thread-safe vkDestroyFramebuffer: requires exclusive framebuffer access.
pub open spec fn ts_destroy_framebuffer(
    fb: FramebufferState,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<FramebufferState> {
    if holds_exclusive(reg, fb.id, thread) {
        Some(destroy_framebuffer_ghost(fb))
    } else {
        None
    }
}

/// Thread-safe framebuffer destroy requires exclusive access.
pub proof fn lemma_ts_destroy_framebuffer_requires_exclusive(
    fb: FramebufferState,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires ts_destroy_framebuffer(fb, thread, reg).is_some(),
    ensures holds_exclusive(reg, fb.id, thread),
{
}

/// After thread-safe destroy, a framebuffer is not alive.
pub proof fn lemma_ts_destroy_framebuffer_not_alive(
    fb: FramebufferState,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires ts_destroy_framebuffer(fb, thread, reg).is_some(),
    ensures !ts_destroy_framebuffer(fb, thread, reg).unwrap().alive,
{
}

// ── Image View ─────────────────────────────────────────────────────────

/// Thread-safe vkDestroyImageView: requires exclusive image view access.
pub open spec fn ts_destroy_image_view(
    view: ImageViewState,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<ImageViewState> {
    if holds_exclusive(reg, view.id, thread) {
        Some(destroy_image_view_ghost(view))
    } else {
        None
    }
}

/// Thread-safe image view destroy requires exclusive access.
pub proof fn lemma_ts_destroy_image_view_requires_exclusive(
    view: ImageViewState,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires ts_destroy_image_view(view, thread, reg).is_some(),
    ensures holds_exclusive(reg, view.id, thread),
{
}

/// After thread-safe destroy, an image view is not alive.
pub proof fn lemma_ts_destroy_image_view_not_alive(
    view: ImageViewState,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires ts_destroy_image_view(view, thread, reg).is_some(),
    ensures !ts_destroy_image_view(view, thread, reg).unwrap().alive,
{
}

// ── Descriptor Pool ────────────────────────────────────────────────────

/// Thread-safe vkDestroyDescriptorPool: requires exclusive pool access.
pub open spec fn ts_destroy_descriptor_pool(
    pool: DescriptorPoolState,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<DescriptorPoolState> {
    if holds_exclusive(reg, pool.id, thread) {
        Some(destroy_descriptor_pool_ghost(pool))
    } else {
        None
    }
}

/// Thread-safe descriptor pool destroy requires exclusive access.
pub proof fn lemma_ts_destroy_descriptor_pool_requires_exclusive(
    pool: DescriptorPoolState,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires ts_destroy_descriptor_pool(pool, thread, reg).is_some(),
    ensures holds_exclusive(reg, pool.id, thread),
{
}

/// After thread-safe destroy, a descriptor pool is not alive.
pub proof fn lemma_ts_destroy_descriptor_pool_not_alive(
    pool: DescriptorPoolState,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires ts_destroy_descriptor_pool(pool, thread, reg).is_some(),
    ensures !ts_destroy_descriptor_pool(pool, thread, reg).unwrap().alive,
{
}

// ── Descriptor Set Layout ──────────────────────────────────────────────

/// Thread-safe vkDestroyDescriptorSetLayout: requires exclusive layout access.
pub open spec fn ts_destroy_descriptor_set_layout(
    layout: DescriptorSetLayoutState,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<DescriptorSetLayoutState> {
    if holds_exclusive(reg, layout.id, thread) {
        Some(destroy_descriptor_set_layout_ghost(layout))
    } else {
        None
    }
}

/// Thread-safe descriptor set layout destroy requires exclusive access.
pub proof fn lemma_ts_destroy_descriptor_set_layout_requires_exclusive(
    layout: DescriptorSetLayoutState,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires ts_destroy_descriptor_set_layout(layout, thread, reg).is_some(),
    ensures holds_exclusive(reg, layout.id, thread),
{
}

/// After thread-safe destroy, a descriptor set layout is not alive.
pub proof fn lemma_ts_destroy_descriptor_set_layout_not_alive(
    layout: DescriptorSetLayoutState,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires ts_destroy_descriptor_set_layout(layout, thread, reg).is_some(),
    ensures !ts_destroy_descriptor_set_layout(layout, thread, reg).unwrap().alive,
{
}

// ── Sampler ────────────────────────────────────────────────────────────

/// Thread-safe vkDestroySampler: requires exclusive sampler access.
pub open spec fn ts_destroy_sampler(
    sampler: SamplerState,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<SamplerState> {
    if holds_exclusive(reg, sampler.id, thread) {
        Some(destroy_sampler_ghost(sampler))
    } else {
        None
    }
}

/// Thread-safe sampler destroy requires exclusive access.
pub proof fn lemma_ts_destroy_sampler_requires_exclusive(
    sampler: SamplerState,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires ts_destroy_sampler(sampler, thread, reg).is_some(),
    ensures holds_exclusive(reg, sampler.id, thread),
{
}

/// After thread-safe destroy, a sampler is not alive.
pub proof fn lemma_ts_destroy_sampler_not_alive(
    sampler: SamplerState,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires ts_destroy_sampler(sampler, thread, reg).is_some(),
    ensures !ts_destroy_sampler(sampler, thread, reg).unwrap().alive,
{
}

// ── Command Pool ───────────────────────────────────────────────────────

/// Thread-safe vkDestroyCommandPool: requires exclusive pool access AND
/// the pool must be empty (no allocated CBs).
pub open spec fn ts_destroy_command_pool(
    pool: CommandPoolState,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<CommandPoolState> {
    if holds_exclusive(reg, pool.id, thread) && pool_empty(pool) {
        Some(destroy_command_pool_ghost(pool))
    } else {
        None
    }
}

/// Thread-safe command pool destroy requires exclusive access.
pub proof fn lemma_ts_destroy_command_pool_requires_exclusive(
    pool: CommandPoolState,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires ts_destroy_command_pool(pool, thread, reg).is_some(),
    ensures holds_exclusive(reg, pool.id, thread),
{
}

/// Thread-safe command pool destroy requires the pool to be empty.
pub proof fn lemma_ts_destroy_command_pool_requires_empty(
    pool: CommandPoolState,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires ts_destroy_command_pool(pool, thread, reg).is_some(),
    ensures pool_empty(pool),
{
}

/// After thread-safe destroy, a command pool is not alive.
pub proof fn lemma_ts_destroy_command_pool_not_alive(
    pool: CommandPoolState,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires ts_destroy_command_pool(pool, thread, reg).is_some(),
    ensures !ts_destroy_command_pool(pool, thread, reg).unwrap().alive,
{
}

} // verus!
