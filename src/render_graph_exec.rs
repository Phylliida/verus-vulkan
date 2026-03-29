use vstd::prelude::*;
use crate::render_graph::*;
use crate::resource::*;

verus! {

//  ── Types ───────────────────────────────────────────────────────────────

///  Execution state of a render graph: tracks which passes have been
///  completed and which resources are ready.
pub struct GraphExecutionState {
    ///  Which passes have been completed (by index).
    pub completed_passes: Set<nat>,
    ///  Which resources are available (written by completed passes).
    pub available_resources: Set<ResourceId>,
}

//  ── Spec Functions ──────────────────────────────────────────────────────

///  Initial execution state: nothing completed, no resources ready.
pub open spec fn initial_execution_state() -> GraphExecutionState {
    GraphExecutionState {
        completed_passes: Set::empty(),
        available_resources: Set::empty(),
    }
}

///  A pass is ready to execute: all of its input dependencies are available.
pub open spec fn pass_ready(
    graph: RenderGraph,
    state: GraphExecutionState,
    pass_idx: nat,
) -> bool
    recommends pass_idx < graph.passes.len(),
{
    //  All edges pointing to this pass have their source pass completed
    forall|e: int| #![trigger graph.edges[e]]
        0 <= e < graph.edges.len()
        && graph.edges[e].to_pass == pass_idx
        ==> state.completed_passes.contains(graph.edges[e].from_pass)
}

///  Execute a single pass: mark it completed and add its output resources.
pub open spec fn execute_pass(
    graph: RenderGraph,
    state: GraphExecutionState,
    pass_idx: nat,
) -> GraphExecutionState
    recommends pass_idx < graph.passes.len(),
{
    let pass = graph.passes[pass_idx as int];
    GraphExecutionState {
        completed_passes: state.completed_passes.insert(pass_idx),
        available_resources: state.available_resources.union(pass.writes),
    }
}

///  Execute passes in a given order (topological).
pub open spec fn execute_in_order(
    graph: RenderGraph,
    order: Seq<nat>,
) -> GraphExecutionState
    decreases order.len(),
{
    if order.len() == 0 {
        initial_execution_state()
    } else {
        execute_pass(
            graph,
            execute_in_order(graph, order.drop_last()),
            order.last(),
        )
    }
}

///  All passes in the graph have been completed.
pub open spec fn all_passes_completed(
    graph: RenderGraph,
    state: GraphExecutionState,
) -> bool {
    forall|i: nat| i < graph.passes.len()
        ==> state.completed_passes.contains(i)
}

///  Whether a value appears somewhere in the order sequence.
pub open spec fn order_contains(order: Seq<nat>, v: nat) -> bool {
    exists|j: int| 0 <= j < order.len() && order[j] == v
}

///  A topological order is valid for execution: each pass's dependencies
///  appear earlier in the order.
pub open spec fn valid_execution_order(
    graph: RenderGraph,
    order: Seq<nat>,
) -> bool {
    //  All passes are included
    order.len() == graph.passes.len()
    //  Each pass appears exactly once (it's a permutation)
    && (forall|i: nat| #![trigger order_contains(order, i)]
        i < graph.passes.len()
        ==> order_contains(order, i))
    //  Dependencies come before dependents
    && (forall|e: int| #![trigger graph.edges[e]]
        0 <= e < graph.edges.len()
        ==> {
            let from_pos = seq_index_of(order, graph.edges[e].from_pass);
            let to_pos = seq_index_of(order, graph.edges[e].to_pass);
            from_pos < to_pos
        })
}

///  Find the first index of a value in a sequence.
pub open spec fn seq_index_of(s: Seq<nat>, v: nat) -> int {
    choose|i: int| 0 <= i < s.len() && s[i] == v
}

///  All passes are distinct in the order (no duplicates).
pub open spec fn order_distinct(order: Seq<nat>) -> bool {
    forall|i: int, j: int|
        0 <= i < order.len() && 0 <= j < order.len() && i != j
        ==> order[i] != order[j]
}

///  After executing k passes in a valid order, the first k passes
///  are completed.
pub open spec fn prefix_completed(
    graph: RenderGraph,
    order: Seq<nat>,
    k: nat,
) -> bool
    recommends k <= order.len(),
{
    forall|i: int| 0 <= i < k
        ==> execute_in_order(graph, order.subrange(0, k as int))
            .completed_passes.contains(order[i])
}

//  ── Proofs ──────────────────────────────────────────────────────────────

///  After executing a pass, it is in the completed set.
pub proof fn lemma_execute_completes_pass(
    graph: RenderGraph,
    state: GraphExecutionState,
    pass_idx: nat,
)
    requires pass_idx < graph.passes.len(),
    ensures
        execute_pass(graph, state, pass_idx)
            .completed_passes.contains(pass_idx),
{
}

///  After executing a pass, previously completed passes remain completed.
pub proof fn lemma_execute_preserves_completed(
    graph: RenderGraph,
    state: GraphExecutionState,
    pass_idx: nat,
    other: nat,
)
    requires
        pass_idx < graph.passes.len(),
        state.completed_passes.contains(other),
    ensures
        execute_pass(graph, state, pass_idx)
            .completed_passes.contains(other),
{
}

///  After executing a pass, its output resources are available.
pub proof fn lemma_execute_makes_resources_available(
    graph: RenderGraph,
    state: GraphExecutionState,
    pass_idx: nat,
    r: ResourceId,
)
    requires
        pass_idx < graph.passes.len(),
        graph.passes[pass_idx as int].writes.contains(r),
    ensures
        execute_pass(graph, state, pass_idx)
            .available_resources.contains(r),
{
}

///  After executing a pass, previously available resources remain available.
pub proof fn lemma_execute_preserves_available(
    graph: RenderGraph,
    state: GraphExecutionState,
    pass_idx: nat,
    r: ResourceId,
)
    requires
        pass_idx < graph.passes.len(),
        state.available_resources.contains(r),
    ensures
        execute_pass(graph, state, pass_idx)
            .available_resources.contains(r),
{
}

///  Executing all passes in order completes all passes.
pub proof fn lemma_full_execution_completes_all(
    graph: RenderGraph,
    order: Seq<nat>,
    k: nat,
)
    requires
        order_distinct(order),
        k <= order.len(),
        forall|i: int| 0 <= i < order.len()
            ==> order[i] < graph.passes.len(),
    ensures
        forall|i: int| 0 <= i < k
            ==> execute_in_order(graph, order.subrange(0, k as int))
                .completed_passes.contains(order[i]),
    decreases k,
{
    if k == 0 {
        //  Nothing to prove
    } else {
        //  Inductive step: first k-1 passes are completed, then executing pass k-1 adds it
        let prefix_k = order.subrange(0, k as int);
        let prefix_km1 = order.subrange(0, (k - 1) as int);

        //  IH: first k-1 passes are completed after executing prefix_km1
        lemma_full_execution_completes_all(graph, order, (k - 1) as nat);
        let state_km1 = execute_in_order(graph, prefix_km1);

        //  prefix_k.drop_last() == prefix_km1
        assert(prefix_k.drop_last() =~= prefix_km1);
        //  prefix_k.last() == order[(k-1)]
        assert(prefix_k.last() == order[(k - 1) as int]);

        //  So execute_in_order(graph, prefix_k) = execute_pass(graph, state_km1, order[k-1])
        let state_k = execute_pass(graph, state_km1, order[(k - 1) as int]);

        //  The k-th pass (at index k-1) is now completed
        lemma_execute_completes_pass(graph, state_km1, order[(k - 1) as int]);

        //  All previous passes remain completed
        assert forall|i: int| 0 <= i < k
        implies state_k.completed_passes.contains(order[i]) by {
            if i < (k - 1) as int {
                //  From IH: state_km1 has order[i]
                assert(state_km1.completed_passes.contains(order[i]));
                //  execute_pass preserves it
                lemma_execute_preserves_completed(graph, state_km1, order[(k - 1) as int], order[i]);
            } else {
                //  i == k-1: just completed
            }
        }
    }
}

///  An initial execution state has no completed passes.
pub proof fn lemma_initial_nothing_completed()
    ensures
        initial_execution_state().completed_passes == Set::<nat>::empty(),
        initial_execution_state().available_resources == Set::<ResourceId>::empty(),
{
}

///  Executing a single pass from the initial state.
pub proof fn lemma_single_pass_execution(
    graph: RenderGraph,
    pass_idx: nat,
)
    requires
        pass_idx < graph.passes.len(),
    ensures ({
        let result = execute_pass(graph, initial_execution_state(), pass_idx);
        result.completed_passes.contains(pass_idx)
        && result.available_resources == graph.passes[pass_idx as int].writes
    }),
{
    let result = execute_pass(graph, initial_execution_state(), pass_idx);
    assert(result.available_resources =~= graph.passes[pass_idx as int].writes);
}

} //  verus!
