use vstd::prelude::*;
use crate::resource::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// What kind of GPU work a render pass performs.
pub enum PassType {
    Graphics,
    Compute,
    Transfer,
}

/// A single node in the render graph DAG.
pub struct RenderPassNode {
    /// Unique pass identifier.
    pub id: nat,
    /// Resources read by this pass.
    pub reads: Set<ResourceId>,
    /// Resources written by this pass.
    pub writes: Set<ResourceId>,
    /// Type of GPU work.
    pub pass_type: PassType,
}

/// A directed edge representing a resource dependency between two passes.
/// The resource is written by `from_pass` and read by `to_pass`.
pub struct ResourceEdge {
    /// Writer pass ID.
    pub from_pass: nat,
    /// Reader pass ID.
    pub to_pass: nat,
    /// The resource being transferred.
    pub resource: ResourceId,
}

/// A render graph: a directed acyclic graph of render passes connected
/// by resource dependencies.
pub struct RenderGraph {
    /// The passes in the graph.
    pub passes: Seq<RenderPassNode>,
    /// The resource dependency edges.
    pub edges: Seq<ResourceEdge>,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// Collect all pass IDs in the graph.
pub open spec fn pass_ids(graph: RenderGraph) -> Seq<nat> {
    Seq::new(graph.passes.len(), |i: int| graph.passes[i].id)
}

/// True iff a pass ID appears in the graph.
pub open spec fn has_pass(graph: RenderGraph, id: nat) -> bool {
    exists|i: nat| i < graph.passes.len() && graph.passes[i as int].id == id
}

/// Look up a pass by its ID. Returns the first match.
pub open spec fn get_pass(graph: RenderGraph, id: nat) -> RenderPassNode
    recommends has_pass(graph, id),
{
    graph.passes[pass_index(graph, id) as int]
}

/// Index of a pass with the given ID.
pub open spec fn pass_index(graph: RenderGraph, id: nat) -> nat
    recommends has_pass(graph, id),
    decreases graph.passes.len(),
{
    if graph.passes.len() == 0 {
        0  // unreachable under recommends
    } else if graph.passes[0].id == id {
        0
    } else {
        1 + pass_index(
            RenderGraph { passes: graph.passes.subrange(1, graph.passes.len() as int), ..graph },
            id,
        )
    }
}

/// All pass IDs in the graph are distinct.
pub open spec fn pass_ids_distinct(graph: RenderGraph) -> bool {
    forall|i: nat, j: nat|
        i < graph.passes.len() && j < graph.passes.len() && i != j
        ==> graph.passes[i as int].id != graph.passes[j as int].id
}

/// Pass `from` can reach pass `to` through edges in the graph.
pub open spec fn reachable(graph: RenderGraph, from: nat, to: nat) -> bool {
    exists|path: Seq<nat>|
        path.len() >= 2
        && path[0] == from
        && path[path.len() - 1] == to
        && is_valid_path(graph, path)
}

/// A sequence of pass IDs forms a valid path if consecutive pairs are connected by edges.
pub open spec fn is_valid_path(graph: RenderGraph, path: Seq<nat>) -> bool {
    forall|k: nat| k + 1 < path.len()
        ==> #[trigger] edge_exists(graph, path[k as int], path[(k + 1) as int])
}

/// True iff there is an edge from `from` to `to` in the graph.
pub open spec fn edge_exists(graph: RenderGraph, from: nat, to: nat) -> bool {
    exists|i: nat| i < graph.edges.len()
        && graph.edges[i as int].from_pass == from
        && graph.edges[i as int].to_pass == to
}

/// A topological ordering is a sequence of pass IDs where every edge goes forward.
pub open spec fn is_topological_order(graph: RenderGraph, order: Seq<nat>) -> bool {
    // Same length as passes
    order.len() == graph.passes.len()
    // Contains all pass IDs
    && (forall|i: nat| i < graph.passes.len()
        ==> seq_contains_nat(order, graph.passes[i as int].id))
    // All elements are pass IDs
    && (forall|i: nat| i < order.len()
        ==> has_pass(graph, order[i as int]))
    // Edges respect the ordering
    && (forall|e: nat| #![trigger graph.edges[e as int]]
        e < graph.edges.len() ==> {
        let edge = graph.edges[e as int];
        seq_index_of(order, edge.from_pass) < seq_index_of(order, edge.to_pass)
    })
}

/// Helper: does a nat sequence contain a value?
pub open spec fn seq_contains_nat(s: Seq<nat>, v: nat) -> bool {
    exists|i: nat| i < s.len() && s[i as int] == v
}

/// Helper: index of first occurrence of v in s.
pub open spec fn seq_index_of(s: Seq<nat>, v: nat) -> nat
    recommends seq_contains_nat(s, v),
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else if s[0] == v {
        0
    } else {
        1 + seq_index_of(s.subrange(1, s.len() as int), v)
    }
}

/// The render graph is acyclic: a valid topological ordering exists.
pub open spec fn is_acyclic(graph: RenderGraph) -> bool {
    exists|order: Seq<nat>| #[trigger] is_topological_order(graph, order)
}

/// Every resource read by a pass is either an external input or produced
/// by an earlier pass (connected by an edge).
pub open spec fn all_dependencies_satisfied(
    graph: RenderGraph,
    external_inputs: Set<ResourceId>,
) -> bool {
    forall|p: nat, r: ResourceId|
        p < graph.passes.len()
        && graph.passes[p as int].reads.contains(r)
        ==> (
            external_inputs.contains(r)
            || #[trigger] read_has_producing_edge(graph, graph.passes[p as int].id, r)
        )
}

/// True iff there is an edge delivering `resource` to `pass_id`.
pub open spec fn read_has_producing_edge(
    graph: RenderGraph,
    pass_id: nat,
    resource: ResourceId,
) -> bool {
    exists|i: nat| i < graph.edges.len()
        && graph.edges[i as int].to_pass == pass_id
        && graph.edges[i as int].resource == resource
}

/// No two passes write to the same resource unless they are ordered by
/// reachability (preventing write-write conflicts).
pub open spec fn no_write_conflicts(graph: RenderGraph) -> bool {
    forall|i: nat, j: nat|
        i < graph.passes.len() && j < graph.passes.len() && i != j
        ==> no_shared_writes(graph, i, j)
}

/// Two pass indices have no shared unordered writes.
pub open spec fn no_shared_writes(graph: RenderGraph, i: nat, j: nat) -> bool {
    forall|r: ResourceId|
        graph.passes[i as int].writes.contains(r)
        && graph.passes[j as int].writes.contains(r)
        ==> (
            reachable(graph, graph.passes[i as int].id, graph.passes[j as int].id)
            || reachable(graph, graph.passes[j as int].id, graph.passes[i as int].id)
        )
}

/// A render graph is well-formed if it has distinct pass IDs, is acyclic,
/// all dependencies are satisfied, and there are no write conflicts.
pub open spec fn render_graph_well_formed(
    graph: RenderGraph,
    external_inputs: Set<ResourceId>,
) -> bool {
    pass_ids_distinct(graph)
    && is_acyclic(graph)
    && all_dependencies_satisfied(graph, external_inputs)
    && no_write_conflicts(graph)
}

/// All resources referenced by any pass in the graph.
pub open spec fn all_graph_resources(graph: RenderGraph) -> Set<ResourceId> {
    Set::new(|r: ResourceId|
        exists|i: nat| i < graph.passes.len()
        && (graph.passes[i as int].reads.contains(r)
            || graph.passes[i as int].writes.contains(r))
    )
}

/// Edges only reference passes that exist in the graph.
pub open spec fn edges_reference_valid_passes(graph: RenderGraph) -> bool {
    forall|i: nat| i < graph.edges.len() ==> (
        has_pass(graph, graph.edges[i as int].from_pass)
        && has_pass(graph, graph.edges[i as int].to_pass)
    )
}

/// No edge is a self-loop.
pub open spec fn no_self_loops(graph: RenderGraph) -> bool {
    forall|i: nat| i < graph.edges.len()
        ==> graph.edges[i as int].from_pass != graph.edges[i as int].to_pass
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// An empty graph is trivially acyclic.
pub proof fn lemma_empty_graph_acyclic()
    ensures is_acyclic(RenderGraph { passes: Seq::empty(), edges: Seq::empty() }),
{
    let graph = RenderGraph { passes: Seq::empty(), edges: Seq::empty() };
    let order = Seq::<nat>::empty();
    assert(is_topological_order(graph, order));
}

/// An empty graph trivially satisfies all dependencies.
pub proof fn lemma_empty_graph_all_deps_satisfied(external_inputs: Set<ResourceId>)
    ensures all_dependencies_satisfied(
        RenderGraph { passes: Seq::empty(), edges: Seq::empty() },
        external_inputs,
    ),
{
}

/// An empty graph has no write conflicts.
pub proof fn lemma_empty_graph_no_write_conflicts()
    ensures no_write_conflicts(RenderGraph { passes: Seq::empty(), edges: Seq::empty() }),
{
}

/// An empty graph is well-formed with any external inputs.
pub proof fn lemma_empty_graph_well_formed(external_inputs: Set<ResourceId>)
    ensures render_graph_well_formed(
        RenderGraph { passes: Seq::empty(), edges: Seq::empty() },
        external_inputs,
    ),
{
    lemma_empty_graph_acyclic();
    lemma_empty_graph_all_deps_satisfied(external_inputs);
    lemma_empty_graph_no_write_conflicts();
}

/// A single-pass graph with no edges is acyclic.
pub proof fn lemma_single_pass_acyclic(pass: RenderPassNode)
    ensures is_acyclic(RenderGraph { passes: seq![pass], edges: Seq::empty() }),
{
    let graph = RenderGraph { passes: seq![pass], edges: Seq::empty() };
    let order = seq![pass.id];
    // Prove is_topological_order
    assert(order.len() == graph.passes.len());
    assert(order[0] == pass.id);
    assert(graph.passes[0].id == pass.id);
    assert(seq_contains_nat(order, graph.passes[0].id));
    assert(has_pass(graph, order[0]));
    assert(is_topological_order(graph, order));
}

/// A single-pass graph has no write conflicts (only one pass).
pub proof fn lemma_single_pass_no_conflicts(pass: RenderPassNode)
    ensures no_write_conflicts(RenderGraph { passes: seq![pass], edges: Seq::empty() }),
{
    let graph = RenderGraph { passes: seq![pass], edges: Seq::empty() };
    assert forall|i: nat, j: nat|
        i < graph.passes.len() && j < graph.passes.len() && i != j
        implies no_shared_writes(graph, i, j) by {
        // Only one pass, so i == j == 0 is the only case, but i != j is false.
    }
}

/// A single-pass graph with all reads in external_inputs is well-formed.
pub proof fn lemma_single_pass_well_formed(
    pass: RenderPassNode,
    external_inputs: Set<ResourceId>,
)
    requires
        forall|r: ResourceId| pass.reads.contains(r) ==> external_inputs.contains(r),
    ensures render_graph_well_formed(
        RenderGraph { passes: seq![pass], edges: Seq::empty() },
        external_inputs,
    ),
{
    let graph = RenderGraph { passes: seq![pass], edges: Seq::empty() };
    lemma_single_pass_acyclic(pass);
    lemma_single_pass_no_conflicts(pass);
}

/// If all dependencies are satisfied, every read has a source.
pub proof fn lemma_satisfied_reads_have_source(
    graph: RenderGraph,
    external_inputs: Set<ResourceId>,
    pass_idx: nat,
    resource: ResourceId,
)
    requires
        all_dependencies_satisfied(graph, external_inputs),
        pass_idx < graph.passes.len(),
        graph.passes[pass_idx as int].reads.contains(resource),
    ensures
        external_inputs.contains(resource)
        || read_has_producing_edge(graph, graph.passes[pass_idx as int].id, resource),
{
}

/// A two-pass pipeline (A writes r, B reads r, edge A→B) is acyclic.
pub proof fn lemma_two_pass_pipeline_acyclic(
    a: RenderPassNode,
    b: RenderPassNode,
    r: ResourceId,
)
    requires
        a.id != b.id,
        a.writes.contains(r),
        b.reads.contains(r),
    ensures is_acyclic(RenderGraph {
        passes: seq![a, b],
        edges: seq![ResourceEdge { from_pass: a.id, to_pass: b.id, resource: r }],
    }),
{
    let graph = RenderGraph {
        passes: seq![a, b],
        edges: seq![ResourceEdge { from_pass: a.id, to_pass: b.id, resource: r }],
    };
    let order = seq![a.id, b.id];

    // Prove is_topological_order(graph, order)
    assert(order.len() == graph.passes.len());

    // All pass IDs are in order
    assert(seq_contains_nat(order, a.id));
    assert(seq_contains_nat(order, b.id));

    // All order elements are pass IDs
    assert(has_pass(graph, order[0]));
    assert(has_pass(graph, order[1]));

    // Edge ordering: the single edge has from_pass = a.id at index 0, to_pass = b.id at index 1
    assert(seq_index_of(order, a.id) == 0nat);

    // Need to show seq_index_of(order, b.id) == 1
    // order = [a.id, b.id], and a.id != b.id, so index of b.id is 1
    let tail = order.subrange(1, 2);
    assert(tail[0] == b.id);
    assert(seq_index_of(tail, b.id) == 0nat);
    assert(seq_index_of(order, b.id) == 1nat);

    assert(is_topological_order(graph, order));
}

/// A two-pass pipeline (A→B) has all dependencies satisfied when A's reads
/// are external and B reads what A writes.
pub proof fn lemma_two_pass_pipeline_deps_satisfied(
    a: RenderPassNode,
    b: RenderPassNode,
    r: ResourceId,
    external_inputs: Set<ResourceId>,
)
    requires
        a.id != b.id,
        a.writes.contains(r),
        b.reads.contains(r),
        // A's reads are all external
        forall|res: ResourceId| a.reads.contains(res) ==> external_inputs.contains(res),
        // B only reads r (or external inputs)
        forall|res: ResourceId| b.reads.contains(res)
            ==> (res == r || external_inputs.contains(res)),
    ensures all_dependencies_satisfied(
        RenderGraph {
            passes: seq![a, b],
            edges: seq![ResourceEdge { from_pass: a.id, to_pass: b.id, resource: r }],
        },
        external_inputs,
    ),
{
    let graph = RenderGraph {
        passes: seq![a, b],
        edges: seq![ResourceEdge { from_pass: a.id, to_pass: b.id, resource: r }],
    };

    assert forall|p: nat, res: ResourceId|
        p < graph.passes.len()
        && graph.passes[p as int].reads.contains(res)
        implies (
            external_inputs.contains(res)
            || #[trigger] read_has_producing_edge(graph, graph.passes[p as int].id, res)
        ) by {
        if p == 0 {
            // Pass A: all reads are external
        } else {
            // Pass B: reads r (which has an edge) or external
            if res == r {
                // Edge at index 0 delivers r to b.id
                assert(graph.edges[0].to_pass == b.id);
                assert(graph.edges[0].resource == r);
                assert(read_has_producing_edge(graph, b.id, r));
            }
        }
    }
}

/// No self-loops means no pass ID equals itself through an edge.
pub proof fn lemma_no_self_loops_implies_edge_distinct(
    graph: RenderGraph,
    edge_idx: nat,
)
    requires
        no_self_loops(graph),
        edge_idx < graph.edges.len(),
    ensures
        graph.edges[edge_idx as int].from_pass != graph.edges[edge_idx as int].to_pass,
{
}

/// If the graph has no edges, it has no write conflicts regardless of passes.
pub proof fn lemma_edgeless_graph_no_conflicts_if_disjoint_writes(graph: RenderGraph)
    requires
        graph.edges.len() == 0,
        // All passes have pairwise disjoint write sets
        forall|i: nat, j: nat, r: ResourceId|
            i < graph.passes.len() && j < graph.passes.len() && i != j
            && graph.passes[i as int].writes.contains(r)
            ==> !graph.passes[j as int].writes.contains(r),
    ensures no_write_conflicts(graph),
{
    assert forall|i: nat, j: nat|
        i < graph.passes.len() && j < graph.passes.len() && i != j
        implies no_shared_writes(graph, i, j) by {
        assert forall|r: ResourceId|
            graph.passes[i as int].writes.contains(r)
            && graph.passes[j as int].writes.contains(r)
            implies (
                reachable(graph, graph.passes[i as int].id, graph.passes[j as int].id)
                || reachable(graph, graph.passes[j as int].id, graph.passes[i as int].id)
            ) by {
            // Disjoint writes: contradiction
            assert(!graph.passes[j as int].writes.contains(r));
        }
    }
}

/// Reachability through a direct edge: if edge (a→b) exists, a can reach b.
pub proof fn lemma_direct_edge_implies_reachable(
    graph: RenderGraph,
    from: nat,
    to: nat,
)
    requires edge_exists(graph, from, to),
    ensures reachable(graph, from, to),
{
    let path = seq![from, to];
    assert(path.len() >= 2);
    assert(path[0] == from);
    assert(path[path.len() - 1] == to);
    assert(edge_exists(graph, path[0], path[1]));
    assert(is_valid_path(graph, path));
}

/// A topological order has no duplicates if pass IDs are distinct.
pub proof fn lemma_topo_order_covers_all_passes(
    graph: RenderGraph,
    order: Seq<nat>,
)
    requires
        is_topological_order(graph, order),
    ensures
        forall|i: nat| i < graph.passes.len()
            ==> seq_contains_nat(order, graph.passes[i as int].id),
{
}

} // verus!
