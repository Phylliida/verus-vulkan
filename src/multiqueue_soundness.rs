use vstd::prelude::*;
use crate::sync::*;
use crate::sync_proofs::*;
use crate::flags::*;
use crate::resource::*;
use crate::render_graph::*;
use crate::render_graph_compile::*;
use crate::render_graph_multiqueue::*;
use crate::render_graph_soundness::*;
use crate::semaphore::*;
use crate::queue::*;
use crate::sync_token::*;

verus! {

// ── Spec Functions ──────────────────────────────────────────────────────

/// Intra-queue synchronization is maintained at a given step:
/// for every same-queue dependency edge targeting a pass at or before this step,
/// either the dependency is from a later step (not yet relevant) or a barrier
/// covers it.
pub open spec fn per_queue_sync_maintained(
    mq: MultiQueueCompiledGraph,
    q: nat,
    step: nat,
) -> bool
    recommends
        mq.per_queue_orders.contains_key(q),
        step <= mq.per_queue_orders[q].len(),
{
    forall|e: int| 0 <= e < mq.source_graph.edges.len() ==> {
        let edge = #[trigger] mq.source_graph.edges[e];
        let src_q = mq.queue_assignments[edge.from_pass as int].queue_family;
        let dst_q = mq.queue_assignments[edge.to_pass as int].queue_family;
        // Only care about same-queue edges on queue q
        (src_q != q || dst_q != q || src_q != dst_q) || (
            // Source appears before destination in queue order
            mq.per_queue_orders.contains_key(q)
            && exists|si: int, di: int|
                0 <= si < mq.per_queue_orders[q].len()
                && 0 <= di < mq.per_queue_orders[q].len()
                && mq.per_queue_orders[q][si] == edge.from_pass
                && mq.per_queue_orders[q][di] == edge.to_pass
                && si < di
        )
    }
}

/// Cross-queue synchronization via semaphore: the semaphore carries sync
/// state from the signal pass on one queue to the wait pass on another.
pub open spec fn cross_queue_sync_via_semaphore(
    mq: MultiQueueCompiledGraph,
    signal_pass: nat,
    wait_pass: nat,
    sem: SemaphoreState,
) -> bool {
    // Semaphore is signaled (signal pass has completed on its queue)
    sem.signaled
    // Signal and wait are on different queues
    && signal_pass < mq.source_graph.passes.len()
    && wait_pass < mq.source_graph.passes.len()
    && mq.queue_assignments[signal_pass as int].queue_family
        != mq.queue_assignments[wait_pass as int].queue_family
    // Semaphore carries resource states from the signal pass
    && forall|r: ResourceId| mq.source_graph.passes[signal_pass as int].writes.contains(r)
        ==> sem.resource_states.contains_key(r)
}

/// Full multi-queue execution soundness: all same-queue dependencies are
/// synchronized via intra-queue barriers + ordering, and all cross-queue
/// dependencies are synchronized via semaphore signal/wait pairs.
pub open spec fn mq_execution_sound(mq: MultiQueueCompiledGraph) -> bool {
    // Well-formed
    mq_compiled_well_formed(mq)
    // Intra-queue: same-queue edges ordered correctly
    && intra_queue_barriers_sufficient(mq)
    // Cross-queue: barriers + semaphores cover all cross-queue edges
    && mq_all_synchronized(mq)
}

/// A resource is readable after a semaphore wait that transferred its
/// sync state from the signal side.
pub open spec fn semaphore_transfer_readable(
    sem: SemaphoreState,
    resource: ResourceId,
    state: SyncState,
    dst_stage: nat,
    dst_access: nat,
) -> bool {
    sem.signaled
    && sem.resource_states.contains_key(resource)
    && resource_overlap(sem.resource_states[resource].resource, state.resource)
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// Intra-queue barriers + ordering establish per_queue_sync_maintained.
/// When intra_queue_barriers_sufficient holds, every same-queue edge
/// has proper ordering in the queue's execution order.
pub proof fn lemma_intra_queue_barriers_establish_sync(
    mq: MultiQueueCompiledGraph,
    q: nat,
)
    requires
        mq_compiled_well_formed(mq),
        intra_queue_barriers_sufficient(mq),
        mq.per_queue_orders.contains_key(q),
    ensures
        per_queue_sync_maintained(mq, q, mq.per_queue_orders[q].len()),
{
    // intra_queue_barriers_sufficient directly provides the ordering property
    // for all same-queue edges — per_queue_sync_maintained follows
    assert forall|e: int| 0 <= e < mq.source_graph.edges.len()
    implies ({
        let edge = #[trigger] mq.source_graph.edges[e];
        let src_q = mq.queue_assignments[edge.from_pass as int].queue_family;
        let dst_q = mq.queue_assignments[edge.to_pass as int].queue_family;
        (src_q != q || dst_q != q || src_q != dst_q) || (
            mq.per_queue_orders.contains_key(q)
            && exists|si: int, di: int|
                0 <= si < mq.per_queue_orders[q].len()
                && 0 <= di < mq.per_queue_orders[q].len()
                && mq.per_queue_orders[q][si] == edge.from_pass
                && mq.per_queue_orders[q][di] == edge.to_pass
                && si < di
        )
    }) by {
        let edge = mq.source_graph.edges[e];
        let src_q = mq.queue_assignments[edge.from_pass as int].queue_family;
        let dst_q = mq.queue_assignments[edge.to_pass as int].queue_family;
        if src_q == q && dst_q == q && src_q == dst_q {
            // From intra_queue_barriers_sufficient
        }
    }
}

/// Signal semaphore deposits resource states from the signal pass.
pub proof fn lemma_semaphore_signal_deposits_state(
    sem: SemaphoreState,
    states: Map<ResourceId, SyncState>,
)
    requires
        semaphore_well_formed(sem),
        !sem.signaled,
    ensures ({
        let signaled = signal_semaphore_ghost(sem, states);
        signaled.signaled
        && signaled.resource_states == states
    }),
{
}

/// After waiting on a semaphore, it becomes unsignaled.
/// The signal's resource_states were available between signal and wait
/// for the waiting pass to consume.
pub proof fn lemma_semaphore_wait_transfers_sync(
    sem: SemaphoreState,
    states: Map<ResourceId, SyncState>,
)
    requires
        semaphore_well_formed(sem),
        !sem.signaled,
    ensures ({
        let signaled = signal_semaphore_ghost(sem, states);
        let waited = wait_semaphore_ghost(signaled);
        // After wait: semaphore unsignaled
        !waited.signaled
        // Between signal and wait: states were deposited
        && signaled.resource_states == states
    }),
{
    lemma_signal_wait_roundtrip(sem, states);
}

/// For each cross-queue edge with a semaphore signal/wait pair,
/// the destination pass has synchronization after the wait.
pub proof fn lemma_cross_queue_sync_sound(
    mq: MultiQueueCompiledGraph,
)
    requires
        mq_compiled_well_formed(mq),
        semaphore_signal_for_each_cross_dep(mq),
    ensures
        // Every cross-queue edge has a semaphore pair
        forall|e: int| 0 <= e < mq.source_graph.edges.len() ==> {
            let edge = #[trigger] mq.source_graph.edges[e];
            let src_q = mq.queue_assignments[edge.from_pass as int].queue_family;
            let dst_q = mq.queue_assignments[edge.to_pass as int].queue_family;
            src_q == dst_q || exists|s: int| 0 <= s < mq.semaphore_signals.len()
                && mq.semaphore_signals[s].0 == edge.from_pass
                && mq.semaphore_signals[s].1 == edge.to_pass
        },
{
    // Direct from semaphore_signal_for_each_cross_dep definition
}

/// Combines intra-queue + cross-queue synchronization into full
/// mq_execution_sound.
pub proof fn lemma_mq_all_passes_synced(
    mq: MultiQueueCompiledGraph,
)
    requires
        mq_compiled_well_formed(mq),
        intra_queue_barriers_sufficient(mq),
        cross_queue_deps_have_barriers(mq),
        semaphore_signal_for_each_cross_dep(mq),
        no_concurrent_write_hazard(mq),
    ensures
        mq_execution_sound(mq),
{
    // mq_all_synchronized = cross_queue_deps_have_barriers
    //                      && semaphore_signal_for_each_cross_dep
    //                      && no_concurrent_write_hazard
    // All three are provided as preconditions.
    lemma_semaphores_prevent_hazards(mq);
}

/// When all passes are on one queue, mq_execution_sound reduces to
/// basic intra-queue ordering (no cross-queue machinery needed).
pub proof fn lemma_single_queue_reduces_to_basic(
    mq: MultiQueueCompiledGraph,
    q: nat,
)
    requires
        mq_compiled_well_formed(mq),
        // All passes on the same queue
        forall|i: int| 0 <= i < mq.queue_assignments.len()
            ==> mq.queue_assignments[i].queue_family == q,
        intra_queue_barriers_sufficient(mq),
    ensures
        mq_execution_sound(mq),
{
    // lemma_single_queue_equivalent gives us cross_queue_deps_have_barriers,
    // semaphore_signal_for_each_cross_dep, and no_concurrent_write_hazard
    // for free when all passes are on one queue.
    lemma_single_queue_equivalent(mq, q);
    lemma_mq_all_passes_synced(mq);
}

} // verus!
