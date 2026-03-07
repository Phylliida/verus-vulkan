use vstd::prelude::*;
use crate::sync_token::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// Generic pool ownership: a pool owns a set of children.
///
/// Models the Vulkan pattern where command pools own command buffers
/// and descriptor pools own descriptor sets. The pool owner has
/// implicit access to all children (transitive synchronization).
///
/// Per the Vulkan spec: "When a commandBuffer parameter needs to be
/// externally synchronized, it implies that the commandPool from which
/// that command buffer was allocated also needs to be externally
/// synchronized."
pub struct PoolOwnership {
    /// The pool's object id.
    pub pool_id: nat,
    /// The thread that owns this pool.
    pub owner: ThreadId,
    /// Children allocated from this pool.
    pub children: Set<nat>,
}

/// Thread-local pool assignment for parallel work.
///
/// Each thread gets its own pool for safe parallel recording/updating.
/// This is the standard Vulkan pattern: 1 thread = 1 command pool.
pub struct ParallelPoolState {
    /// Per-thread pool assignments.
    pub assignments: Map<ThreadId, PoolOwnership>,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// A thread can access a child if it either:
/// 1. Holds an exclusive token on the child directly, OR
/// 2. Owns the parent pool (transitive/implicit sync).
///
/// This matches the Vulkan spec's implicit external synchronization.
pub open spec fn can_access_child(
    pool: PoolOwnership,
    child_id: nat,
    thread: ThreadId,
    reg: TokenRegistry,
) -> bool {
    pool.children.contains(child_id)
    && (
        // Direct exclusive access to the child
        holds_exclusive(reg, child_id, thread)
        // Or implicit access via pool ownership
        || pool.owner == thread
    )
}

/// A thread can mutate the pool itself (reset, destroy, allocate from).
pub open spec fn can_mutate_pool(
    pool: PoolOwnership,
    thread: ThreadId,
    reg: TokenRegistry,
) -> bool {
    pool.owner == thread
    && holds_exclusive(reg, pool.pool_id, thread)
}

/// Allocate a new child from the pool.
pub open spec fn pool_allocate(
    pool: PoolOwnership,
    child_id: nat,
) -> PoolOwnership {
    PoolOwnership {
        children: pool.children.insert(child_id),
        ..pool
    }
}

/// Free a child from the pool.
pub open spec fn pool_free(
    pool: PoolOwnership,
    child_id: nat,
) -> PoolOwnership {
    PoolOwnership {
        children: pool.children.remove(child_id),
        ..pool
    }
}

/// Reset pool: all children return to pool control, none externally held.
pub open spec fn pool_reset_safe(
    pool: PoolOwnership,
    reg: TokenRegistry,
) -> bool {
    // No child is exclusively held by any thread
    forall|child: nat| pool.children.contains(child)
        ==> object_available(reg, child)
}

/// After reset, the pool has no children.
pub open spec fn pool_reset(pool: PoolOwnership) -> PoolOwnership {
    PoolOwnership {
        children: Set::empty(),
        ..pool
    }
}

/// No two threads share a pool in parallel pool state.
pub open spec fn pools_disjoint(state: ParallelPoolState) -> bool {
    forall|t1: ThreadId, t2: ThreadId|
        state.assignments.contains_key(t1)
        && state.assignments.contains_key(t2)
        && t1 != t2
        ==> state.assignments[t1].pool_id != state.assignments[t2].pool_id
}

/// No two threads' pools share any children.
pub open spec fn children_disjoint(state: ParallelPoolState) -> bool {
    forall|t1: ThreadId, t2: ThreadId|
        state.assignments.contains_key(t1)
        && state.assignments.contains_key(t2)
        && t1 != t2
        ==> state.assignments[t1].children.disjoint(
            state.assignments[t2].children)
}

/// The parallel pool state is safe: disjoint pools and disjoint children.
pub open spec fn parallel_pools_safe(state: ParallelPoolState) -> bool {
    pools_disjoint(state) && children_disjoint(state)
}

/// An empty pool for a thread.
pub open spec fn empty_pool(
    thread: ThreadId,
    pool_id: nat,
) -> PoolOwnership {
    PoolOwnership {
        pool_id,
        owner: thread,
        children: Set::empty(),
    }
}

/// A thread begins using a child (e.g., starts recording a CB).
pub open spec fn begin_child_use(
    pool: PoolOwnership,
    child_id: nat,
) -> PoolOwnership {
    PoolOwnership {
        children: pool.children.insert(child_id),
        ..pool
    }
}

/// A thread finishes using a child (e.g., ends recording a CB).
pub open spec fn end_child_use(
    pool: PoolOwnership,
    child_id: nat,
) -> PoolOwnership {
    PoolOwnership {
        children: pool.children.remove(child_id),
        ..pool
    }
}

/// Concurrent child access from different pools is safe.
pub open spec fn concurrent_child_access_safe(
    pool1: PoolOwnership,
    pool2: PoolOwnership,
    child1: nat,
    child2: nat,
) -> bool {
    pool1.pool_id != pool2.pool_id
    && pool1.children.contains(child1)
    && pool2.children.contains(child2)
    && child1 != child2
}

/// Queue submission context: submitter holds queue, CBs not held by others.
pub open spec fn submit_from_pools_safe(
    state: ParallelPoolState,
    queue_id: nat,
    submitter: ThreadId,
    cb_ids: Seq<nat>,
    reg: TokenRegistry,
) -> bool {
    // Submitter has exclusive queue access
    holds_exclusive(reg, queue_id, submitter)
    // All submitted CBs are not exclusively held by other threads
    && (forall|i: int| #![trigger cb_ids[i]]
        0 <= i < cb_ids.len() ==>
        not_held_by_other(reg, cb_ids[i], submitter))
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// Pool owner can always access any child (implicit sync).
pub proof fn lemma_owner_can_access_child(
    pool: PoolOwnership,
    child_id: nat,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires
        pool.owner == thread,
        pool.children.contains(child_id),
    ensures
        can_access_child(pool, child_id, thread, reg),
{
}

/// Pool mutation requires exclusive pool token.
pub proof fn lemma_pool_mutate_requires_token(
    pool: PoolOwnership,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires
        can_mutate_pool(pool, thread, reg),
    ensures
        holds_exclusive(reg, pool.pool_id, thread),
{
}

/// Disjoint pools ensure different children don't race.
pub proof fn lemma_disjoint_pools_no_race(
    pool1: PoolOwnership,
    pool2: PoolOwnership,
    child1: nat,
    child2: nat,
)
    requires
        pool1.pool_id != pool2.pool_id,
        pool1.children.contains(child1),
        pool2.children.contains(child2),
        child1 != child2,
    ensures
        concurrent_child_access_safe(pool1, pool2, child1, child2),
{
}

/// Disjoint parallel pools ensure no child overlap.
pub proof fn lemma_parallel_no_child_race(
    state: ParallelPoolState,
    t1: ThreadId,
    t2: ThreadId,
    child: nat,
)
    requires
        parallel_pools_safe(state),
        state.assignments.contains_key(t1),
        state.assignments.contains_key(t2),
        t1 != t2,
        state.assignments[t1].children.contains(child),
    ensures
        !state.assignments[t2].children.contains(child),
{
    assert(state.assignments[t1].children.disjoint(
        state.assignments[t2].children));
}

/// Empty pools from different threads are trivially disjoint.
pub proof fn lemma_empty_pools_disjoint(
    t1: ThreadId,
    t2: ThreadId,
    p1: nat,
    p2: nat,
)
    requires t1 != t2, p1 != p2,
    ensures
        empty_pool(t1, p1).pool_id != empty_pool(t2, p2).pool_id,
        empty_pool(t1, p1).children.disjoint(
            empty_pool(t2, p2).children),
{
    assert(empty_pool(t1, p1).children =~= Set::<nat>::empty());
    assert(empty_pool(t2, p2).children =~= Set::<nat>::empty());
}

/// Allocating a child adds it to the pool.
pub proof fn lemma_allocate_adds_child(
    pool: PoolOwnership,
    child_id: nat,
)
    ensures
        pool_allocate(pool, child_id).children.contains(child_id),
{
}

/// Freeing a child removes it from the pool.
pub proof fn lemma_free_removes_child(
    pool: PoolOwnership,
    child_id: nat,
)
    ensures
        !pool_free(pool, child_id).children.contains(child_id),
{
}

/// Allocating preserves existing children.
pub proof fn lemma_allocate_preserves_others(
    pool: PoolOwnership,
    child_id: nat,
    other_id: nat,
)
    requires pool.children.contains(other_id),
    ensures pool_allocate(pool, child_id).children.contains(other_id),
{
}

/// Reset clears all children.
pub proof fn lemma_reset_clears_children(
    pool: PoolOwnership,
    child: nat,
)
    ensures
        !pool_reset(pool).children.contains(child),
{
}

/// If pool reset is safe, all children are available.
pub proof fn lemma_reset_safe_means_available(
    pool: PoolOwnership,
    reg: TokenRegistry,
    child: nat,
)
    requires
        pool_reset_safe(pool, reg),
        pool.children.contains(child),
    ensures
        object_available(reg, child),
{
}

/// Queue submission with exclusive queue token blocks others from the queue.
pub proof fn lemma_submit_exclusive_queue(
    state: ParallelPoolState,
    queue_id: nat,
    submitter: ThreadId,
    other: ThreadId,
    cb_ids: Seq<nat>,
    reg: TokenRegistry,
)
    requires
        submit_from_pools_safe(state, queue_id, submitter, cb_ids, reg),
        other != submitter,
    ensures
        !holds_exclusive(reg, queue_id, other),
{
}

} // verus!
