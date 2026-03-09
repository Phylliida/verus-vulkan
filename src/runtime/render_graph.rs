use vstd::prelude::*;
use crate::resource::*;
use crate::render_graph::*;
use crate::render_graph_compile::*;

verus! {

/// Runtime builder for constructing a render graph.
pub struct RuntimeRenderGraphBuilder {
    /// Ghost model of the render graph being built.
    pub state: Ghost<RenderGraph>,
}

impl View for RuntimeRenderGraphBuilder {
    type V = RenderGraph;
    open spec fn view(&self) -> RenderGraph { self.state@ }
}

/// Runtime wrapper for a compiled render graph with runtime metadata.
pub struct RuntimeCompiledGraphWrapper {
    /// Ghost compiled graph.
    pub compiled: Ghost<CompiledGraph>,
    /// Number of passes in the graph (runtime-accessible).
    pub num_passes: usize,
    /// Number of barriers per step (runtime-accessible).
    pub step_barrier_counts: Vec<usize>,
}

/// Exec: create an empty render graph builder.
pub fn create_graph_builder_exec() -> (out: RuntimeRenderGraphBuilder)
    ensures
        out@.passes.len() == 0,
        out@.edges.len() == 0,
{
    RuntimeRenderGraphBuilder {
        state: Ghost(RenderGraph {
            passes: Seq::empty(),
            edges: Seq::empty(),
        }),
    }
}

/// Exec: add a render pass to the graph.
pub fn add_pass_exec(
    builder: &mut RuntimeRenderGraphBuilder,
    pass: Ghost<RenderPassNode>,
)
    requires !has_pass(old(builder)@, pass@.id),
    ensures
        builder@.passes == old(builder)@.passes.push(pass@),
        builder@.edges == old(builder)@.edges,
{
    builder.state = Ghost(RenderGraph {
        passes: builder.state@.passes.push(pass@),
        edges: builder.state@.edges,
    });
}

/// Exec: add a resource dependency edge to the graph.
pub fn add_edge_exec(
    builder: &mut RuntimeRenderGraphBuilder,
    edge: Ghost<ResourceEdge>,
)
    requires
        has_pass(old(builder)@, edge@.from_pass),
        has_pass(old(builder)@, edge@.to_pass),
        edge@.from_pass != edge@.to_pass,
    ensures
        builder@.edges == old(builder)@.edges.push(edge@),
        builder@.passes == old(builder)@.passes,
{
    builder.state = Ghost(RenderGraph {
        passes: builder.state@.passes,
        edges: builder.state@.edges.push(edge@),
    });
}

/// Exec: package a compiled graph with runtime metadata.
///
/// The compilation itself is done at the spec level; this function bridges
/// the ghost CompiledGraph with runtime-accessible counts for the executor.
pub fn compile_graph_exec(
    builder: &RuntimeRenderGraphBuilder,
    external_inputs: Ghost<Set<ResourceId>>,
    cg: Ghost<CompiledGraph>,
    num_passes: usize,
    step_barrier_counts: Vec<usize>,
) -> (out: RuntimeCompiledGraphWrapper)
    requires
        render_graph_well_formed(builder@, external_inputs@),
        compiled_graph_well_formed(cg@),
        cg@.source_graph == builder@,
        num_passes as nat == builder@.passes.len(),
        step_barrier_counts@.len() == cg@.barrier_plans.len(),
    ensures
        out.compiled@ == cg@,
        out.num_passes == num_passes,
        out.step_barrier_counts@.len() == cg@.barrier_plans.len(),
{
    RuntimeCompiledGraphWrapper {
        compiled: cg,
        num_passes,
        step_barrier_counts,
    }
}

/// Exec: validate that the compiled graph is well-formed.
pub fn validate_compiled_graph_exec(
    wrapper: &RuntimeCompiledGraphWrapper,
) -> (result: Ghost<bool>)
    ensures result@ ==> compiled_graph_well_formed(wrapper.compiled@),
{
    Ghost(compiled_graph_well_formed(wrapper.compiled@))
}

/// Proof: an empty graph can be compiled to a trivially well-formed compiled graph.
pub proof fn lemma_empty_graph_compiles(external_inputs: Set<ResourceId>)
    ensures ({
        let empty_graph = RenderGraph { passes: Seq::empty(), edges: Seq::empty() };
        let cg = CompiledGraph {
            source_graph: empty_graph,
            execution_order: Seq::empty(),
            barrier_plans: Seq::empty(),
            resource_lifetimes: Map::empty(),
        };
        render_graph_well_formed(empty_graph, external_inputs)
        && compiled_graph_well_formed(cg)
    }),
{
    lemma_empty_graph_well_formed(external_inputs);
}

} // verus!
