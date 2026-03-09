use vstd::prelude::*;
use crate::command::*;
use crate::sync_token::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// Ghost state for a Vulkan command pool (VkCommandPool).
///
/// A command pool manages the memory for command buffers. Resetting
/// the pool resets all allocated command buffers to Initial state.
pub struct CommandPoolState {
    pub id: nat,
    /// Queue family this pool is associated with.
    pub queue_family: nat,
    /// Set of command buffer IDs allocated from this pool.
    pub allocated_cbs: Set<nat>,
    /// Whether the pool allows individual CB reset.
    pub individual_reset: bool,
    /// Whether the pool is alive.
    pub alive: bool,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// Create a fresh command pool.
pub open spec fn create_command_pool(
    id: nat,
    queue_family: nat,
    individual_reset: bool,
) -> CommandPoolState {
    CommandPoolState {
        id,
        queue_family,
        allocated_cbs: Set::empty(),
        individual_reset,
        alive: true,
    }
}

/// Allocate a command buffer from the pool.
///
/// Per Vulkan spec: "commandPool is an externally synchronized parameter"
/// for vkAllocateCommandBuffers.
pub open spec fn allocate_cb(
    pool: CommandPoolState,
    cb_id: nat,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<CommandPoolState> {
    if !holds_exclusive(reg, pool.id, thread) {
        None
    } else {
        Some(CommandPoolState {
            allocated_cbs: pool.allocated_cbs.insert(cb_id),
            ..pool
        })
    }
}

/// Free a command buffer back to the pool.
///
/// Per Vulkan spec: "commandPool is an externally synchronized parameter"
/// for vkFreeCommandBuffers.
pub open spec fn free_cb(
    pool: CommandPoolState,
    cb_id: nat,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<CommandPoolState> {
    if !holds_exclusive(reg, pool.id, thread) {
        None
    } else {
        Some(CommandPoolState {
            allocated_cbs: pool.allocated_cbs.remove(cb_id),
            ..pool
        })
    }
}

/// Reset pool: all allocated CBs go to Initial state.
/// Returns the set of CBs that need to be reset.
///
/// Per Vulkan spec: "commandPool is an externally synchronized parameter"
/// for vkResetCommandPool.
pub open spec fn reset_pool_cbs(
    pool: CommandPoolState,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<Set<nat>> {
    if !holds_exclusive(reg, pool.id, thread) {
        None
    } else {
        Some(pool.allocated_cbs)
    }
}

/// After pool reset, all CBs are in Initial state.
pub open spec fn all_cbs_initial_after_reset(
    pool: CommandPoolState,
    cb_states: Map<nat, CommandBufferState>,
) -> bool {
    forall|cb: nat| pool.allocated_cbs.contains(cb)
        && cb_states.contains_key(cb)
        ==> cb_states[cb] == CommandBufferState::Initial
}

/// Individual reset is allowed for a CB from this pool.
pub open spec fn individual_reset_allowed(
    pool: CommandPoolState,
    cb_id: nat,
) -> bool {
    pool.individual_reset && pool.allocated_cbs.contains(cb_id)
}

/// A CB belongs to this pool.
pub open spec fn cb_from_pool(
    pool: CommandPoolState,
    cb_id: nat,
) -> bool {
    pool.allocated_cbs.contains(cb_id)
}

/// Pool is well-formed.
pub open spec fn command_pool_well_formed(pool: CommandPoolState) -> bool {
    pool.alive
}

/// No CBs are allocated from this pool (safe to destroy).
pub open spec fn pool_empty(pool: CommandPoolState) -> bool {
    pool.allocated_cbs == Set::<nat>::empty()
}

/// Ghost update: destroy a command pool.
/// Per Vulkan spec: pool must have no allocated CBs outstanding.
pub open spec fn destroy_command_pool_ghost(
    pool: CommandPoolState,
) -> CommandPoolState {
    CommandPoolState {
        alive: false,
        ..pool
    }
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// A fresh pool has no allocated CBs.
pub proof fn lemma_fresh_pool_empty(
    id: nat,
    queue_family: nat,
    individual_reset: bool,
)
    ensures pool_empty(create_command_pool(id, queue_family, individual_reset)),
{
}

/// After allocating, the CB is in the pool.
pub proof fn lemma_allocate_adds_cb(
    pool: CommandPoolState,
    cb_id: nat,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires holds_exclusive(reg, pool.id, thread),
    ensures cb_from_pool(allocate_cb(pool, cb_id, thread, reg).unwrap(), cb_id),
{
}

/// After freeing, the CB is not in the pool.
pub proof fn lemma_free_removes_cb(
    pool: CommandPoolState,
    cb_id: nat,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires holds_exclusive(reg, pool.id, thread),
    ensures !cb_from_pool(free_cb(pool, cb_id, thread, reg).unwrap(), cb_id),
{
}

/// Allocating preserves existing CBs.
pub proof fn lemma_allocate_preserves_existing(
    pool: CommandPoolState,
    cb_id: nat,
    other: nat,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires
        cb_from_pool(pool, other),
        holds_exclusive(reg, pool.id, thread),
    ensures cb_from_pool(allocate_cb(pool, cb_id, thread, reg).unwrap(), other),
{
}

/// Freeing preserves other CBs.
pub proof fn lemma_free_preserves_others(
    pool: CommandPoolState,
    cb_id: nat,
    other: nat,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires
        cb_from_pool(pool, other),
        other != cb_id,
        holds_exclusive(reg, pool.id, thread),
    ensures cb_from_pool(free_cb(pool, cb_id, thread, reg).unwrap(), other),
{
}

/// Pool reset returns all allocated CBs.
pub proof fn lemma_reset_returns_all(
    pool: CommandPoolState,
    cb_id: nat,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires
        cb_from_pool(pool, cb_id),
        holds_exclusive(reg, pool.id, thread),
    ensures reset_pool_cbs(pool, thread, reg).unwrap().contains(cb_id),
{
}

/// A fresh pool is well-formed.
pub proof fn lemma_fresh_pool_well_formed(
    id: nat,
    queue_family: nat,
    individual_reset: bool,
)
    ensures
        command_pool_well_formed(
            create_command_pool(id, queue_family, individual_reset)),
{
}

/// Without exclusive pool access, allocate fails.
pub proof fn lemma_no_access_no_allocate(
    pool: CommandPoolState,
    cb_id: nat,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires !holds_exclusive(reg, pool.id, thread),
    ensures allocate_cb(pool, cb_id, thread, reg).is_none(),
{
}

/// Without exclusive pool access, reset fails.
pub proof fn lemma_no_access_no_reset(
    pool: CommandPoolState,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires !holds_exclusive(reg, pool.id, thread),
    ensures reset_pool_cbs(pool, thread, reg).is_none(),
{
}

/// After destroying, a command pool is not alive.
pub proof fn lemma_destroy_command_pool_not_alive(pool: CommandPoolState)
    ensures !destroy_command_pool_ghost(pool).alive,
{
}

/// Destroying a command pool preserves its id.
pub proof fn lemma_destroy_command_pool_preserves_id(pool: CommandPoolState)
    ensures destroy_command_pool_ghost(pool).id == pool.id,
{
}

} // verus!
