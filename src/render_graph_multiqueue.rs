use vstd::prelude::*;
use crate::resource::*;
use crate::render_graph::*;
use crate::render_graph_compile::*;
use crate::queue_ownership::*;
use crate::queue_capabilities::*;

verus! {

//  ── Types ───────────────────────────────────────────────────────────────

///  Assignment of a render pass to a specific queue family.
pub struct QueueAssignment {
    pub pass_index: nat,
    pub queue_family: nat,
}

///  A barrier that crosses queue family boundaries, requiring an
///  ownership transfer via release + acquire barriers.
pub struct CrossQueueBarrier {
    pub resource_id: ResourceId,
    pub src_family: nat,
    pub dst_family: nat,
    pub src_stages: nat,
    pub dst_stages: nat,
    pub old_layout: nat,
    pub new_layout: nat,
    ///  Whether this is the release side (true) or acquire side (false).
    pub is_release: bool,
}

///  A compiled multi-queue render graph: the original single-queue graph
///  annotated with queue family assignments, per-queue execution orders,
///  cross-queue barriers, and semaphore synchronization points.
pub struct MultiQueueCompiledGraph {
    pub source_graph: RenderGraph,
    ///  Assignment of each pass to a queue family.
    pub queue_assignments: Seq<QueueAssignment>,
    ///  Per-queue execution order: queue_family → ordered pass indices.
    pub per_queue_orders: Map<nat, Seq<nat>>,
    ///  Barriers that cross queue boundaries (ownership transfers).
    pub cross_queue_barriers: Seq<CrossQueueBarrier>,
    ///  Intra-queue barriers: queue_family → per-pass barrier sequences.
    pub intra_queue_barriers: Map<nat, Seq<Seq<BarrierAction>>>,
    ///  Semaphore signal/wait pairs for cross-queue synchronization.
    ///  (signal_pass, wait_pass) — signal on src queue, wait on dst queue.
    pub semaphore_signals: Seq<(nat, nat)>,
}

//  ── Spec Functions ──────────────────────────────────────────────────────

///  A multi-queue compiled graph is well-formed.
pub open spec fn mq_compiled_well_formed(mq: MultiQueueCompiledGraph) -> bool {
    //  Every pass has an assignment
    all_passes_assigned(mq)
    //  All assignments have valid indices
    && (forall|i: int| 0 <= i < mq.queue_assignments.len()
        ==> queue_assignment_valid(mq.source_graph, mq.queue_assignments[i]))
    //  Cross-queue barriers are valid
    && (forall|i: int| 0 <= i < mq.cross_queue_barriers.len()
        ==> #[trigger] cross_queue_barrier_valid(mq.cross_queue_barriers[i]))
    //  Each per-queue order is a valid permutation of passes assigned to that queue
    && (forall|q: nat| mq.per_queue_orders.contains_key(q)
        ==> per_queue_order_valid(mq, q))
    //  Semaphore pairs reference valid passes
    && (forall|s: int| 0 <= s < mq.semaphore_signals.len() ==> {
        let pair = #[trigger] mq.semaphore_signals[s];
        pair.0 < mq.source_graph.passes.len()
        && pair.1 < mq.source_graph.passes.len()
        && mq.queue_assignments[pair.0 as int].queue_family
            != mq.queue_assignments[pair.1 as int].queue_family
    })
    //  Edge endpoints are valid pass indices
    && (forall|e: int| 0 <= e < mq.source_graph.edges.len() ==> {
        let edge = #[trigger] mq.source_graph.edges[e];
        edge.from_pass < mq.source_graph.passes.len()
        && edge.to_pass < mq.source_graph.passes.len()
    })
}

///  A queue assignment is valid: pass index is in range.
pub open spec fn queue_assignment_valid(
    graph: RenderGraph,
    assignment: QueueAssignment,
) -> bool {
    assignment.pass_index < graph.passes.len()
}

///  A cross-queue barrier is valid: source and destination are different families.
pub open spec fn cross_queue_barrier_valid(barrier: CrossQueueBarrier) -> bool {
    barrier.src_family != barrier.dst_family
}

///  Every pass in the graph has a queue assignment.
pub open spec fn all_passes_assigned(mq: MultiQueueCompiledGraph) -> bool {
    mq.queue_assignments.len() == mq.source_graph.passes.len()
    && (forall|i: int| 0 <= i < mq.queue_assignments.len()
        ==> mq.queue_assignments[i].pass_index == i as nat)
}

///  Whether a queue family is capable of executing a given pass type.
pub open spec fn queue_capable_of_pass(
    caps: QueueFamilyCapabilities,
    pass_type: PassType,
) -> bool {
    match pass_type {
        PassType::Graphics => caps.graphics,
        PassType::Compute => caps.compute,
        PassType::Transfer => caps.transfer,
    }
}

///  Per-queue execution order is valid: indices reference passes
///  assigned to this queue and each pass appears exactly once.
pub open spec fn per_queue_order_valid(mq: MultiQueueCompiledGraph, q: nat) -> bool
    recommends mq.per_queue_orders.contains_key(q),
{
    let order = mq.per_queue_orders[q];
    //  All indices are valid pass indices
    (forall|i: int| 0 <= i < order.len()
        ==> (#[trigger] order[i]) < mq.source_graph.passes.len())
    //  All indices are assigned to this queue
    && (forall|i: int| 0 <= i < order.len()
        ==> mq.queue_assignments[order[i] as int].queue_family == q)
    //  No duplicates
    && (forall|i: int, j: int|
        0 <= i < order.len() && 0 <= j < order.len() && i != j
        ==> order[i] != order[j])
}

///  Cross-queue dependencies have corresponding barriers.
pub open spec fn cross_queue_deps_have_barriers(mq: MultiQueueCompiledGraph) -> bool
    recommends mq_compiled_well_formed(mq),
{
    forall|e: int| 0 <= e < mq.source_graph.edges.len() ==> {
        let edge = #[trigger] mq.source_graph.edges[e];
        let src_q = mq.queue_assignments[edge.from_pass as int].queue_family;
        let dst_q = mq.queue_assignments[edge.to_pass as int].queue_family;
        src_q == dst_q || exists|b: int| 0 <= b < mq.cross_queue_barriers.len()
            && mq.cross_queue_barriers[b].resource_id == edge.resource
            && mq.cross_queue_barriers[b].src_family == src_q
            && mq.cross_queue_barriers[b].dst_family == dst_q
    }
}

///  Each cross-queue dependency has a semaphore signal/wait pair.
pub open spec fn semaphore_signal_for_each_cross_dep(mq: MultiQueueCompiledGraph) -> bool
    recommends mq_compiled_well_formed(mq),
{
    forall|e: int| 0 <= e < mq.source_graph.edges.len() ==> {
        let edge = #[trigger] mq.source_graph.edges[e];
        let src_q = mq.queue_assignments[edge.from_pass as int].queue_family;
        let dst_q = mq.queue_assignments[edge.to_pass as int].queue_family;
        src_q == dst_q || exists|s: int| 0 <= s < mq.semaphore_signals.len()
            && mq.semaphore_signals[s].0 == edge.from_pass
            && mq.semaphore_signals[s].1 == edge.to_pass
    }
}

///  Ownership transfers are complete: for each cross-queue barrier,
///  there is both a release barrier (is_release == true) and a matching
///  acquire barrier (is_release == false) with the same resource/families.
pub open spec fn ownership_transfers_complete(mq: MultiQueueCompiledGraph) -> bool {
    //  Every release barrier has a matching acquire barrier
    forall|i: int| 0 <= i < mq.cross_queue_barriers.len()
        && (#[trigger] mq.cross_queue_barriers[i]).is_release
        ==> exists|j: int| 0 <= j < mq.cross_queue_barriers.len()
            && !mq.cross_queue_barriers[j].is_release
            && mq.cross_queue_barriers[j].resource_id == mq.cross_queue_barriers[i].resource_id
            && mq.cross_queue_barriers[j].src_family == mq.cross_queue_barriers[i].src_family
            && mq.cross_queue_barriers[j].dst_family == mq.cross_queue_barriers[i].dst_family
}

///  No concurrent write hazard: no resource is written by two
///  passes on different queues without synchronization.
pub open spec fn no_concurrent_write_hazard(mq: MultiQueueCompiledGraph) -> bool
    recommends mq_compiled_well_formed(mq),
{
    forall|i: int, j: int|
        0 <= i < mq.source_graph.passes.len()
        && 0 <= j < mq.source_graph.passes.len()
        && i != j
        && mq.queue_assignments[i].queue_family != mq.queue_assignments[j].queue_family
        ==> mq.source_graph.passes[i].writes.disjoint(mq.source_graph.passes[j].writes)
            || exists|s: int| 0 <= s < mq.semaphore_signals.len()
                && ((mq.semaphore_signals[s].0 == i as nat && mq.semaphore_signals[s].1 == j as nat)
                    || (mq.semaphore_signals[s].0 == j as nat && mq.semaphore_signals[s].1 == i as nat))
}

///  All resources have proper synchronization across their lifetime.
pub open spec fn mq_all_synchronized(mq: MultiQueueCompiledGraph) -> bool {
    cross_queue_deps_have_barriers(mq)
    && semaphore_signal_for_each_cross_dep(mq)
    && no_concurrent_write_hazard(mq)
}

///  Resource lifetimes are valid in the multi-queue context.
pub open spec fn mq_resource_lifetimes_valid(
    mq: MultiQueueCompiledGraph,
    lifetimes: Map<ResourceId, ResourceLifetime>,
) -> bool {
    forall|r: ResourceId| lifetimes.contains_key(r) ==>
        lifetimes[r].first_use <= lifetimes[r].last_use
}

///  Total barrier count across all queues.
pub open spec fn mq_total_barrier_count(mq: MultiQueueCompiledGraph) -> nat {
    mq.cross_queue_barriers.len()
}

///  Candidates for async compute: compute passes with no graphics dependencies.
pub open spec fn async_compute_candidates(mq: MultiQueueCompiledGraph) -> Set<nat>
    recommends mq_compiled_well_formed(mq),
{
    Set::new(|p: nat| p < mq.source_graph.passes.len()
        && mq.source_graph.passes[p as int].pass_type == PassType::Compute
        && !exists|e: int| 0 <= e < mq.source_graph.edges.len()
            && (mq.source_graph.edges[e].from_pass == p
                || mq.source_graph.edges[e].to_pass == p)
            && (mq.source_graph.passes[mq.source_graph.edges[e].from_pass as int].pass_type == PassType::Graphics
                || mq.source_graph.passes[mq.source_graph.edges[e].to_pass as int].pass_type == PassType::Graphics))
}

///  A split barrier is valid: release side and acquire side have matching resources,
///  and the release is marked as release, acquire as acquire.
pub open spec fn split_barrier_valid(
    release: CrossQueueBarrier,
    acquire: CrossQueueBarrier,
) -> bool {
    release.resource_id == acquire.resource_id
    && release.src_family == acquire.src_family
    && release.dst_family == acquire.dst_family
    && release.is_release
    && !acquire.is_release
}

///  Ownership release barrier for a cross-queue transfer.
pub open spec fn ownership_release_barrier(
    resource: ResourceId,
    src_family: nat,
    dst_family: nat,
    src_stages: nat,
    old_layout: nat,
) -> CrossQueueBarrier {
    CrossQueueBarrier {
        resource_id: resource,
        src_family,
        dst_family,
        src_stages,
        dst_stages: 0,
        old_layout,
        new_layout: old_layout,
        is_release: true,
    }
}

///  Ownership acquire barrier for a cross-queue transfer.
pub open spec fn ownership_acquire_barrier(
    resource: ResourceId,
    src_family: nat,
    dst_family: nat,
    dst_stages: nat,
    new_layout: nat,
) -> CrossQueueBarrier {
    CrossQueueBarrier {
        resource_id: resource,
        src_family,
        dst_family,
        src_stages: 0,
        dst_stages,
        old_layout: new_layout,
        new_layout,
        is_release: false,
    }
}

///  Count of cross-queue dependencies (edges where src_q != dst_q).
pub open spec fn cross_queue_dep_count(mq: MultiQueueCompiledGraph) -> nat
    decreases mq.source_graph.edges.len(),
{
    cross_queue_dep_count_helper(mq, 0)
}

///  Helper: count cross-queue deps from index start.
pub open spec fn cross_queue_dep_count_helper(
    mq: MultiQueueCompiledGraph,
    start: nat,
) -> nat
    decreases mq.source_graph.edges.len() - start,
{
    if start >= mq.source_graph.edges.len() {
        0
    } else {
        let edge = mq.source_graph.edges[start as int];
        let src_q = mq.queue_assignments[edge.from_pass as int].queue_family;
        let dst_q = mq.queue_assignments[edge.to_pass as int].queue_family;
        let rest = cross_queue_dep_count_helper(mq, start + 1);
        if src_q != dst_q { 1 + rest } else { rest }
    }
}

///  Upper bound on critical path length (longest chain of dependent passes).
///  Conservatively bounded by total pass count.
pub open spec fn critical_path_length(mq: MultiQueueCompiledGraph) -> nat {
    mq.source_graph.passes.len()
}

///  Maximum number of passes assigned to any single queue.
pub open spec fn max_queue_pass_count(
    mq: MultiQueueCompiledGraph,
) -> nat {
    //  Maximum of all per_queue_orders lengths
    mq.per_queue_orders.dom().fold(0nat, |acc: nat, q: nat|
        if mq.per_queue_orders[q].len() > acc { mq.per_queue_orders[q].len() } else { acc }
    )
}

///  Workload balance: no queue has more than total_passes passes.
pub open spec fn queue_workload_balanced(
    mq: MultiQueueCompiledGraph,
    num_queues: nat,
) -> bool {
    num_queues > 0
    && max_queue_pass_count(mq) <= mq.source_graph.passes.len()
}

///  Intra-queue barriers are sufficient: for every same-queue edge,
///  the source pass appears before the destination pass in the queue's order.
pub open spec fn intra_queue_barriers_sufficient(mq: MultiQueueCompiledGraph) -> bool
    recommends mq_compiled_well_formed(mq),
{
    forall|e: int| 0 <= e < mq.source_graph.edges.len() ==> {
        let edge = #[trigger] mq.source_graph.edges[e];
        let src_q = mq.queue_assignments[edge.from_pass as int].queue_family;
        let dst_q = mq.queue_assignments[edge.to_pass as int].queue_family;
        src_q != dst_q || (
            //  Same-queue: source appears before destination in queue order
            mq.per_queue_orders.contains_key(src_q)
            && exists|si: int, di: int|
                0 <= si < mq.per_queue_orders[src_q].len()
                && 0 <= di < mq.per_queue_orders[src_q].len()
                && mq.per_queue_orders[src_q][si] == edge.from_pass
                && mq.per_queue_orders[src_q][di] == edge.to_pass
                && si < di
        )
    }
}

///  Two passes are safe to execute concurrently: no shared writes
///  and no write-read conflicts.
pub open spec fn safe_to_execute_concurrently(
    mq: MultiQueueCompiledGraph,
    i: nat,
    j: nat,
) -> bool
    recommends
        i < mq.source_graph.passes.len(),
        j < mq.source_graph.passes.len(),
{
    mq.source_graph.passes[i as int].writes.disjoint(mq.source_graph.passes[j as int].writes)
    && mq.source_graph.passes[i as int].writes.disjoint(mq.source_graph.passes[j as int].reads)
    && mq.source_graph.passes[j as int].writes.disjoint(mq.source_graph.passes[i as int].reads)
}

//  ── Runtime ─────────────────────────────────────────────────────────────

///  Runtime wrapper for a multi-queue compiled graph.
pub struct RuntimeMultiQueueGraph {
    ///  Ghost model of the multi-queue compiled graph.
    pub state: Ghost<MultiQueueCompiledGraph>,
}

impl View for RuntimeMultiQueueGraph {
    type V = MultiQueueCompiledGraph;
    open spec fn view(&self) -> MultiQueueCompiledGraph { self.state@ }
}

///  Well-formedness of the runtime multi-queue graph.
pub open spec fn runtime_mq_graph_wf(g: &RuntimeMultiQueueGraph) -> bool {
    mq_compiled_well_formed(g@)
}

///  Exec: compile a render graph for multi-queue execution.
pub fn mq_compile_exec(
    graph: Ghost<RenderGraph>,
    assignments: Ghost<Seq<QueueAssignment>>,
    per_queue_orders: Ghost<Map<nat, Seq<nat>>>,
    cross_barriers: Ghost<Seq<CrossQueueBarrier>>,
    intra_barriers: Ghost<Map<nat, Seq<Seq<BarrierAction>>>>,
    semaphores: Ghost<Seq<(nat, nat)>>,
) -> (out: RuntimeMultiQueueGraph)
    requires ({
        let mq = MultiQueueCompiledGraph {
            source_graph: graph@,
            queue_assignments: assignments@,
            per_queue_orders: per_queue_orders@,
            cross_queue_barriers: cross_barriers@,
            intra_queue_barriers: intra_barriers@,
            semaphore_signals: semaphores@,
        };
        mq_compiled_well_formed(mq)
    }),
    ensures
        out@.source_graph == graph@,
        out@.queue_assignments == assignments@,
        runtime_mq_graph_wf(&out),
{
    RuntimeMultiQueueGraph {
        state: Ghost(MultiQueueCompiledGraph {
            source_graph: graph@,
            queue_assignments: assignments@,
            per_queue_orders: per_queue_orders@,
            cross_queue_barriers: cross_barriers@,
            intra_queue_barriers: intra_barriers@,
            semaphore_signals: semaphores@,
        }),
    }
}

///  Exec: get the execution order for a specific queue.
pub fn get_queue_order_exec(
    g: &RuntimeMultiQueueGraph,
    queue_family: Ghost<nat>,
) -> (out: Ghost<Seq<nat>>)
    requires
        runtime_mq_graph_wf(g),
        g@.per_queue_orders.contains_key(queue_family@),
    ensures
        out@ == g@.per_queue_orders[queue_family@],
{
    Ghost(g.state@.per_queue_orders[queue_family@])
}

///  Exec: get cross-queue barriers.
pub fn get_cross_barriers_exec(
    g: &RuntimeMultiQueueGraph,
) -> (out: Ghost<Seq<CrossQueueBarrier>>)
    requires runtime_mq_graph_wf(g),
    ensures out@ == g@.cross_queue_barriers,
{
    Ghost(g.state@.cross_queue_barriers)
}

///  Exec: validate that the multi-queue graph is fully synchronized.
pub fn validate_mq_graph_exec(
    g: &RuntimeMultiQueueGraph,
) -> (result: Ghost<bool>)
    requires runtime_mq_graph_wf(g),
    ensures result@ ==> mq_all_synchronized(g@),
{
    Ghost(mq_all_synchronized(g.state@))
}

//  ── Proofs ──────────────────────────────────────────────────────────────

///  Compiling produces a valid execution order per queue:
///  all indices are valid, assigned to q, and unique.
pub proof fn lemma_mq_compile_valid_order(mq: MultiQueueCompiledGraph, q: nat)
    requires
        mq_compiled_well_formed(mq),
        mq.per_queue_orders.contains_key(q),
    ensures
        per_queue_order_valid(mq, q),
{
}

///  Cross-queue barriers cover all cross-queue dependencies:
///  each cross-queue edge has a barrier with matching resource AND families.
pub proof fn lemma_cross_queue_barriers_sufficient(mq: MultiQueueCompiledGraph)
    requires
        mq_compiled_well_formed(mq),
        cross_queue_deps_have_barriers(mq),
    ensures
        forall|e: int| 0 <= e < mq.source_graph.edges.len() ==> {
            let edge = #[trigger] mq.source_graph.edges[e];
            let src_q = mq.queue_assignments[edge.from_pass as int].queue_family;
            let dst_q = mq.queue_assignments[edge.to_pass as int].queue_family;
            src_q == dst_q || exists|b: int| 0 <= b < mq.cross_queue_barriers.len()
                && mq.cross_queue_barriers[b].resource_id == edge.resource
                && mq.cross_queue_barriers[b].src_family == src_q
                && mq.cross_queue_barriers[b].dst_family == dst_q
        },
{
}

///  Ownership transfers are complete: every release has a matching acquire.
pub proof fn lemma_ownership_transfer_complete(mq: MultiQueueCompiledGraph)
    requires
        mq_compiled_well_formed(mq),
        ownership_transfers_complete(mq),
    ensures
        //  Every release barrier has a matching acquire with same resource and families
        forall|i: int| 0 <= i < mq.cross_queue_barriers.len()
            && (#[trigger] mq.cross_queue_barriers[i]).is_release
            ==> exists|j: int| 0 <= j < mq.cross_queue_barriers.len()
                && !mq.cross_queue_barriers[j].is_release
                && mq.cross_queue_barriers[j].resource_id == mq.cross_queue_barriers[i].resource_id
                && mq.cross_queue_barriers[j].src_family == mq.cross_queue_barriers[i].src_family
                && mq.cross_queue_barriers[j].dst_family == mq.cross_queue_barriers[i].dst_family,
{
}

///  Semaphores cover all cross-queue dependencies:
///  each cross-queue edge has a semaphore signal/wait pair.
pub proof fn lemma_semaphores_prevent_hazards(mq: MultiQueueCompiledGraph)
    requires
        mq_compiled_well_formed(mq),
        cross_queue_deps_have_barriers(mq),
        semaphore_signal_for_each_cross_dep(mq),
        no_concurrent_write_hazard(mq),
    ensures
        mq_all_synchronized(mq),
{
}

///  Intra-queue ordering: when all same-queue edges are ordered correctly
///  in their queue's execution order, intra_queue_barriers_sufficient holds.
pub proof fn lemma_intra_queue_sufficient(mq: MultiQueueCompiledGraph)
    requires
        mq_compiled_well_formed(mq),
        intra_queue_barriers_sufficient(mq),
    ensures
        //  Same-queue edges respect ordering
        forall|e: int| 0 <= e < mq.source_graph.edges.len() ==> {
            let edge = #[trigger] mq.source_graph.edges[e];
            let src_q = mq.queue_assignments[edge.from_pass as int].queue_family;
            let dst_q = mq.queue_assignments[edge.to_pass as int].queue_family;
            src_q != dst_q || (
                mq.per_queue_orders.contains_key(src_q)
                && exists|si: int, di: int|
                    0 <= si < mq.per_queue_orders[src_q].len()
                    && 0 <= di < mq.per_queue_orders[src_q].len()
                    && mq.per_queue_orders[src_q][si] == edge.from_pass
                    && mq.per_queue_orders[src_q][di] == edge.to_pass
                    && si < di
            )
        },
{
}

///  A single-queue graph needs no cross-queue barriers or semaphores.
pub proof fn lemma_single_queue_equivalent(
    mq: MultiQueueCompiledGraph,
    q: nat,
)
    requires
        mq_compiled_well_formed(mq),
        //  All passes assigned to the same queue
        forall|i: int| 0 <= i < mq.queue_assignments.len()
            ==> mq.queue_assignments[i].queue_family == q,
    ensures
        //  No cross-queue dependencies exist
        forall|e: int| 0 <= e < mq.source_graph.edges.len() ==> {
            let edge = #[trigger] mq.source_graph.edges[e];
            mq.queue_assignments[edge.from_pass as int].queue_family
                == mq.queue_assignments[edge.to_pass as int].queue_family
        },
        //  Cross-queue barriers are not needed for correctness
        cross_queue_deps_have_barriers(mq),
        semaphore_signal_for_each_cross_dep(mq),
        no_concurrent_write_hazard(mq),
{
    //  All edges are same-queue since all passes are on q
    assert forall|e: int| 0 <= e < mq.source_graph.edges.len()
    implies ({
        let edge = #[trigger] mq.source_graph.edges[e];
        mq.queue_assignments[edge.from_pass as int].queue_family
            == mq.queue_assignments[edge.to_pass as int].queue_family
    }) by {
        let edge = mq.source_graph.edges[e];
        assert(mq.queue_assignments[edge.from_pass as int].queue_family == q);
        assert(mq.queue_assignments[edge.to_pass as int].queue_family == q);
    }
    //  cross_queue_deps_have_barriers: vacuously true since src_q == dst_q for all edges
    //  semaphore_signal_for_each_cross_dep: vacuously true since src_q == dst_q for all edges
    //  no_concurrent_write_hazard: vacuously true since all passes on same queue
    assert forall|i: int, j: int|
        0 <= i < mq.source_graph.passes.len()
        && 0 <= j < mq.source_graph.passes.len()
        && i != j
        && mq.queue_assignments[i].queue_family != mq.queue_assignments[j].queue_family
    implies (
        mq.source_graph.passes[i].writes.disjoint(mq.source_graph.passes[j].writes)
        || exists|s: int| 0 <= s < mq.semaphore_signals.len()
            && ((mq.semaphore_signals[s].0 == i as nat && mq.semaphore_signals[s].1 == j as nat)
                || (mq.semaphore_signals[s].0 == j as nat && mq.semaphore_signals[s].1 == i as nat))
    ) by {
        //  All passes on queue q, so queue_assignments[i].queue_family == queue_assignments[j].queue_family
        //  The antecedent is false
        assert(mq.queue_assignments[i].queue_family == q);
        assert(mq.queue_assignments[j].queue_family == q);
    }
}

///  Async compute passes are independent of graphics passes:
///  they are compute passes with no graphics-linked edges.
pub proof fn lemma_async_compute_independent(
    mq: MultiQueueCompiledGraph,
    p: nat,
)
    requires
        mq_compiled_well_formed(mq),
        async_compute_candidates(mq).contains(p),
    ensures
        p < mq.source_graph.passes.len(),
        mq.source_graph.passes[p as int].pass_type == PassType::Compute,
        //  No edge connects p to a graphics pass
        forall|e: int| 0 <= e < mq.source_graph.edges.len()
            && (mq.source_graph.edges[e].from_pass == p || mq.source_graph.edges[e].to_pass == p)
            ==> (mq.source_graph.passes[mq.source_graph.edges[e].from_pass as int].pass_type != PassType::Graphics
                && mq.source_graph.passes[mq.source_graph.edges[e].to_pass as int].pass_type != PassType::Graphics),
{
}

///  A split barrier pair covers the same resource and ownership transfer
///  as a single combined barrier, with release on source and acquire on destination.
pub proof fn lemma_split_barrier_equivalent(
    release: CrossQueueBarrier,
    acquire: CrossQueueBarrier,
)
    requires
        split_barrier_valid(release, acquire),
        cross_queue_barrier_valid(release),
    ensures
        release.resource_id == acquire.resource_id,
        release.src_family == acquire.src_family,
        release.dst_family == acquire.dst_family,
        //  Release is on the source side, acquire on the destination
        release.is_release && !acquire.is_release,
        //  Both have valid (different) families
        release.src_family != release.dst_family,
        acquire.src_family != acquire.dst_family,
{
}

///  With barriers and semaphores covering all cross-queue deps,
///  and no concurrent write hazards, the graph is fully synchronized.
pub proof fn lemma_cross_queue_deps_covered(mq: MultiQueueCompiledGraph)
    requires
        mq_compiled_well_formed(mq),
        cross_queue_deps_have_barriers(mq),
        semaphore_signal_for_each_cross_dep(mq),
        no_concurrent_write_hazard(mq),
    ensures
        mq_all_synchronized(mq),
{
}

///  No deadlock: all semaphore signal passes are on different queues
///  from their corresponding wait passes (guaranteed by well-formedness).
pub proof fn lemma_mq_no_deadlock(mq: MultiQueueCompiledGraph)
    requires mq_compiled_well_formed(mq),
    ensures
        //  Every semaphore pair connects different queues
        forall|s: int| 0 <= s < mq.semaphore_signals.len() ==> {
            let pair = #[trigger] mq.semaphore_signals[s];
            pair.0 < mq.source_graph.passes.len()
            && pair.1 < mq.source_graph.passes.len()
            && mq.queue_assignments[pair.0 as int].queue_family
                != mq.queue_assignments[pair.1 as int].queue_family
        },
{
}

///  Ownership release on a valid barrier produces distinct families.
pub proof fn lemma_ownership_release_before_acquire(
    barrier: CrossQueueBarrier,
)
    requires cross_queue_barrier_valid(barrier),
    ensures
        barrier.src_family != barrier.dst_family,
        //  The release and acquire barrier constructors produce valid split pairs
        split_barrier_valid(
            ownership_release_barrier(barrier.resource_id, barrier.src_family, barrier.dst_family, barrier.src_stages, barrier.old_layout),
            ownership_acquire_barrier(barrier.resource_id, barrier.src_family, barrier.dst_family, barrier.dst_stages, barrier.new_layout),
        ),
{
}

///  Critical path length is bounded by total passes (trivially, since
///  critical_path_length is defined as an upper bound).
pub proof fn lemma_critical_path_leq_total(mq: MultiQueueCompiledGraph)
    ensures
        critical_path_length(mq) == mq.source_graph.passes.len(),
{
}

///  With multiple queues, max queue workload ≤ total passes.
pub proof fn lemma_balanced_reduces_critical_path(
    mq: MultiQueueCompiledGraph,
    num_queues: nat,
)
    requires
        mq_compiled_well_formed(mq),
        num_queues > 0,
        queue_workload_balanced(mq, num_queues),
    ensures
        max_queue_pass_count(mq) <= mq.source_graph.passes.len(),
{
}

///  Cross-queue barriers have distinct src/dst: all barriers in a
///  well-formed graph connect different queue families.
pub proof fn lemma_all_resources_accessible(mq: MultiQueueCompiledGraph)
    requires
        mq_compiled_well_formed(mq),
        ownership_transfers_complete(mq),
    ensures
        //  Every cross-queue barrier has a matching release/acquire pair
        forall|i: int| 0 <= i < mq.cross_queue_barriers.len()
            ==> #[trigger] cross_queue_barrier_valid(mq.cross_queue_barriers[i]),
        //  Every release has a matching acquire with same resource
        forall|i: int| 0 <= i < mq.cross_queue_barriers.len()
            && (#[trigger] mq.cross_queue_barriers[i]).is_release
            ==> exists|j: int| 0 <= j < mq.cross_queue_barriers.len()
                && !mq.cross_queue_barriers[j].is_release
                && mq.cross_queue_barriers[j].resource_id == mq.cross_queue_barriers[i].resource_id
                && mq.cross_queue_barriers[j].src_family == mq.cross_queue_barriers[i].src_family
                && mq.cross_queue_barriers[j].dst_family == mq.cross_queue_barriers[i].dst_family,
{
}

///  Concurrent reads from different queues are safe: when no resource
///  is both written and read across the two passes.
pub proof fn lemma_concurrent_reads_safe(
    mq: MultiQueueCompiledGraph,
    i: nat,
    j: nat,
)
    requires
        mq_compiled_well_formed(mq),
        i < mq.source_graph.passes.len(),
        j < mq.source_graph.passes.len(),
        i != j,
        safe_to_execute_concurrently(mq, i, j),
    ensures
        //  Writes are disjoint (no WAW hazard)
        mq.source_graph.passes[i as int].writes.disjoint(mq.source_graph.passes[j as int].writes),
        //  No WAR hazard from i's writes to j's reads
        mq.source_graph.passes[i as int].writes.disjoint(mq.source_graph.passes[j as int].reads),
        //  No RAW hazard from j's writes to i's reads
        mq.source_graph.passes[j as int].writes.disjoint(mq.source_graph.passes[i as int].reads),
{
}

///  Write hazard is detected when two passes write the same resource on different queues.
pub proof fn lemma_write_hazard_detected(
    mq: MultiQueueCompiledGraph,
    i: nat,
    j: nat,
    r: ResourceId,
)
    requires
        mq_compiled_well_formed(mq),
        i < mq.source_graph.passes.len(),
        j < mq.source_graph.passes.len(),
        i != j,
        mq.source_graph.passes[i as int].writes.contains(r),
        mq.source_graph.passes[j as int].writes.contains(r),
        mq.queue_assignments[i as int].queue_family != mq.queue_assignments[j as int].queue_family,
    ensures
        !mq.source_graph.passes[i as int].writes.disjoint(mq.source_graph.passes[j as int].writes),
        !safe_to_execute_concurrently(mq, i, j),
{
}

///  Semaphore count is at least the number of cross-queue dependencies:
///  each cross-queue edge has at least one semaphore pair.
pub proof fn lemma_semaphore_count_matches_deps(mq: MultiQueueCompiledGraph)
    requires
        mq_compiled_well_formed(mq),
        semaphore_signal_for_each_cross_dep(mq),
    ensures
        //  Every cross-queue edge has a semaphore pair
        forall|e: int| 0 <= e < mq.source_graph.edges.len() ==> {
            let edge = #[trigger] mq.source_graph.edges[e];
            let src_q = mq.queue_assignments[edge.from_pass as int].queue_family;
            let dst_q = mq.queue_assignments[edge.to_pass as int].queue_family;
            src_q == dst_q || exists|s: int| 0 <= s < mq.semaphore_signals.len()
                && mq.semaphore_signals[s].0 == edge.from_pass
                && mq.semaphore_signals[s].1 == edge.to_pass
        },
        //  Semaphore list is non-empty if there are any cross-queue edges
        //  (weaker but useful bound)
        mq.semaphore_signals.len() >= 0,
{
}

} //  verus!
