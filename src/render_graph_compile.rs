use vstd::prelude::*;
use crate::resource::*;
use crate::render_graph::*;
use crate::flags::*;

verus! {

//  ── Types ──────────────────────────────────────────────────────────────

///  A barrier to insert between passes for synchronization.
pub struct BarrierAction {
    ///  Resource being synchronized.
    pub resource: ResourceId,
    ///  Source pipeline stages.
    pub src_stages: PipelineStageFlags,
    ///  Source access mask.
    pub src_accesses: AccessFlags,
    ///  Destination pipeline stages.
    pub dst_stages: PipelineStageFlags,
    ///  Destination access mask.
    pub dst_accesses: AccessFlags,
    ///  Image layout before the barrier.
    pub old_layout: nat,
    ///  Image layout after the barrier.
    pub new_layout: nat,
}

///  Barriers required before and after a single pass.
pub struct PassBarrierPlan {
    ///  Index of the pass in the execution order.
    pub pass_index: nat,
    ///  Barriers to insert before the pass executes.
    pub pre_barriers: Seq<BarrierAction>,
    ///  Barriers to insert after the pass executes.
    pub post_barriers: Seq<BarrierAction>,
}

///  Resource lifetime: first and last use in execution order.
pub struct ResourceLifetime {
    ///  Index of the first pass that uses this resource.
    pub first_use: nat,
    ///  Index of the last pass that uses this resource.
    pub last_use: nat,
}

///  A compiled render graph: the original graph plus execution order,
///  per-pass barrier plans, and resource lifetimes.
pub struct CompiledGraph {
    ///  The source render graph.
    pub source_graph: RenderGraph,
    ///  Topological execution order (indices into source_graph.passes).
    pub execution_order: Seq<nat>,
    ///  Barrier plan for each pass in execution order.
    pub barrier_plans: Seq<PassBarrierPlan>,
    ///  Lifetime of each resource (first_use, last_use in execution order).
    pub resource_lifetimes: Map<ResourceId, ResourceLifetime>,
}

//  ── Spec Functions ──────────────────────────────────────────────────

///  A barrier action is well-formed: non-empty stages and accesses.
pub open spec fn barrier_action_well_formed(ba: BarrierAction) -> bool {
    !ba.src_stages.stages.is_empty()
    && !ba.dst_stages.stages.is_empty()
}

///  A pass barrier plan references a valid pass index.
pub open spec fn pass_barrier_plan_well_formed(
    plan: PassBarrierPlan,
    num_passes: nat,
) -> bool {
    plan.pass_index < num_passes
    && (forall|i: nat|
        #![trigger plan.pre_barriers[i as int]]
        i < plan.pre_barriers.len()
        ==> barrier_action_well_formed(plan.pre_barriers[i as int]))
    && (forall|i: nat|
        #![trigger plan.post_barriers[i as int]]
        i < plan.post_barriers.len()
        ==> barrier_action_well_formed(plan.post_barriers[i as int]))
}

///  The execution order contains valid pass indices.
pub open spec fn execution_order_valid(
    graph: RenderGraph,
    order: Seq<nat>,
) -> bool {
    order.len() == graph.passes.len()
    && (forall|i: nat|
        #![trigger order[i as int]]
        i < order.len() ==> order[i as int] < graph.passes.len())
}

///  A compiled graph is well-formed.
pub open spec fn compiled_graph_well_formed(cg: CompiledGraph) -> bool {
    execution_order_valid(cg.source_graph, cg.execution_order)
    && cg.barrier_plans.len() == cg.execution_order.len()
    && (forall|i: nat|
        #![trigger cg.barrier_plans[i as int]]
        i < cg.barrier_plans.len()
        ==> pass_barrier_plan_well_formed(
            cg.barrier_plans[i as int],
            cg.source_graph.passes.len(),
        ))
}

///  True iff pass at `order_idx` writes resource `r`.
pub open spec fn pass_writes_resource(
    graph: RenderGraph,
    order: Seq<nat>,
    order_idx: nat,
    r: ResourceId,
) -> bool
    recommends
        order_idx < order.len(),
        order[order_idx as int] < graph.passes.len(),
{
    graph.passes[order[order_idx as int] as int].writes.contains(r)
}

///  True iff pass at `order_idx` reads resource `r`.
pub open spec fn pass_reads_resource(
    graph: RenderGraph,
    order: Seq<nat>,
    order_idx: nat,
    r: ResourceId,
) -> bool
    recommends
        order_idx < order.len(),
        order[order_idx as int] < graph.passes.len(),
{
    graph.passes[order[order_idx as int] as int].reads.contains(r)
}

///  A resource is used by the pass at `order_idx` (read or write).
pub open spec fn pass_uses_resource(
    graph: RenderGraph,
    order: Seq<nat>,
    order_idx: nat,
    r: ResourceId,
) -> bool
    recommends
        order_idx < order.len(),
        order[order_idx as int] < graph.passes.len(),
{
    pass_reads_resource(graph, order, order_idx, r)
    || pass_writes_resource(graph, order, order_idx, r)
}

///  Index of first use of a resource in execution order.
pub open spec fn resource_first_use(
    graph: RenderGraph,
    order: Seq<nat>,
    r: ResourceId,
) -> nat
    decreases order.len(),
{
    if order.len() == 0 {
        0
    } else if order[0] < graph.passes.len()
        && (graph.passes[order[0] as int].reads.contains(r)
            || graph.passes[order[0] as int].writes.contains(r))
    {
        0
    } else {
        1 + resource_first_use(
            graph,
            order.subrange(1, order.len() as int),
            r,
        )
    }
}

///  Index of last use of a resource in execution order.
pub open spec fn resource_last_use(
    graph: RenderGraph,
    order: Seq<nat>,
    r: ResourceId,
) -> nat
    decreases order.len(),
{
    if order.len() == 0 {
        0
    } else {
        let rest_last = resource_last_use(
            graph,
            order.subrange(1, order.len() as int),
            r,
        );
        let last_idx = order.len() as nat - 1;
        if order[last_idx as int] < graph.passes.len()
            && (graph.passes[order[last_idx as int] as int].reads.contains(r)
                || graph.passes[order[last_idx as int] as int].writes.contains(r))
        {
            last_idx as nat
        } else {
            resource_last_use(graph, order.subrange(0, last_idx as int), r)
        }
    }
}

///  A resource lifetime covers all uses in the execution order.
pub open spec fn lifetime_covers_uses(
    lifetime: ResourceLifetime,
    graph: RenderGraph,
    order: Seq<nat>,
    r: ResourceId,
) -> bool {
    forall|i: nat|
        #![trigger order[i as int]]
        i < order.len()
        && order[i as int] < graph.passes.len()
        && (graph.passes[order[i as int] as int].reads.contains(r)
            || graph.passes[order[i as int] as int].writes.contains(r))
        ==> lifetime.first_use <= i && i <= lifetime.last_use
}

///  Resource lifetimes are valid: every resource's lifetime covers its uses.
pub open spec fn resource_lifetimes_valid(
    cg: CompiledGraph,
) -> bool {
    forall|r: ResourceId|
        #![trigger cg.resource_lifetimes[r]]
        cg.resource_lifetimes.contains_key(r)
        ==> lifetime_covers_uses(
            cg.resource_lifetimes[r],
            cg.source_graph,
            cg.execution_order,
            r,
        )
}

///  Two resources have non-overlapping lifetimes.
pub open spec fn lifetimes_non_overlapping(
    lt1: ResourceLifetime,
    lt2: ResourceLifetime,
) -> bool {
    lt1.last_use < lt2.first_use || lt2.last_use < lt1.first_use
}

///  Two resources can safely alias memory if their lifetimes don't overlap.
pub open spec fn memory_reuse_safe(
    cg: CompiledGraph,
    r1: ResourceId,
    r2: ResourceId,
) -> bool {
    cg.resource_lifetimes.contains_key(r1)
    && cg.resource_lifetimes.contains_key(r2)
    && lifetimes_non_overlapping(
        cg.resource_lifetimes[r1],
        cg.resource_lifetimes[r2],
    )
}

///  A barrier plan has a barrier for every dependency edge targeting this pass.
pub open spec fn barrier_plan_covers_deps(
    plan: PassBarrierPlan,
    graph: RenderGraph,
    pass_idx: nat,
) -> bool {
    forall|e: nat|
        #![trigger graph.edges[e as int]]
        e < graph.edges.len()
        && graph.edges[e as int].to_pass == pass_idx
        ==> (exists|b: nat|
            #![trigger plan.pre_barriers[b as int]]
            b < plan.pre_barriers.len()
            && plan.pre_barriers[b as int].resource
                == graph.edges[e as int].resource)
}

///  All barrier plans cover their dependencies.
pub open spec fn all_barriers_cover_deps(cg: CompiledGraph) -> bool
    recommends compiled_graph_well_formed(cg),
{
    forall|i: nat|
        #![trigger cg.barrier_plans[i as int]]
        i < cg.barrier_plans.len()
        ==> barrier_plan_covers_deps(
            cg.barrier_plans[i as int],
            cg.source_graph,
            cg.execution_order[i as int],
        )
}

///  Count of total barriers in the compiled graph.
pub open spec fn total_barrier_count(cg: CompiledGraph) -> nat
    decreases cg.barrier_plans.len(),
{
    if cg.barrier_plans.len() == 0 {
        0
    } else {
        let last = cg.barrier_plans[cg.barrier_plans.len() - 1];
        last.pre_barriers.len() + last.post_barriers.len()
        + total_barrier_count(CompiledGraph {
            barrier_plans: cg.barrier_plans.subrange(0, cg.barrier_plans.len() as int - 1),
            ..cg
        })
    }
}

//  ── Pass Type → Stage/Access Mapping ────────────────────────────────────
//
//  Default pipeline stages and access flags for each pass type.
//  These map PassType to the appropriate Vulkan sync scope.

///  Default write stages for a pass type.
pub open spec fn pass_type_write_stages(pt: PassType) -> PipelineStageFlags {
    PipelineStageFlags {
        stages: Set::empty().insert(match pt {
            PassType::Graphics => STAGE_COLOR_ATTACHMENT_OUTPUT(),
            PassType::Compute => STAGE_COMPUTE_SHADER(),
            PassType::Transfer => STAGE_TRANSFER(),
        }),
    }
}

///  Default write accesses for a pass type.
pub open spec fn pass_type_write_accesses(pt: PassType) -> AccessFlags {
    AccessFlags {
        accesses: Set::empty().insert(match pt {
            PassType::Graphics => ACCESS_COLOR_ATTACHMENT_WRITE(),
            PassType::Compute => ACCESS_SHADER_WRITE(),
            PassType::Transfer => ACCESS_TRANSFER_WRITE(),
        }),
    }
}

///  Default read stages for a pass type.
pub open spec fn pass_type_read_stages(pt: PassType) -> PipelineStageFlags {
    PipelineStageFlags {
        stages: Set::empty().insert(match pt {
            PassType::Graphics => STAGE_FRAGMENT_SHADER(),
            PassType::Compute => STAGE_COMPUTE_SHADER(),
            PassType::Transfer => STAGE_TRANSFER(),
        }),
    }
}

///  Default read accesses for a pass type.
pub open spec fn pass_type_read_accesses(pt: PassType) -> AccessFlags {
    AccessFlags {
        accesses: Set::empty().insert(match pt {
            PassType::Graphics => ACCESS_SHADER_READ(),
            PassType::Compute => ACCESS_SHADER_READ(),
            PassType::Transfer => ACCESS_TRANSFER_READ(),
        }),
    }
}

///  Compile barriers for a given pass (all dependency edges targeting it).
///  Uses pass types to determine proper pipeline stages and access flags.
pub open spec fn compile_barriers_for_pass(
    graph: RenderGraph,
    pass_idx: nat,
) -> Seq<BarrierAction>
    recommends
        has_pass(graph, pass_idx),
        edges_reference_valid_passes(graph),
{
    Seq::new(
        graph.edges.len(),
        |e: int| {
            let edge = graph.edges[e];
            let src_pass = get_pass(graph, edge.from_pass);
            let dst_pass = get_pass(graph, pass_idx);
            BarrierAction {
                resource: edge.resource,
                src_stages: pass_type_write_stages(src_pass.pass_type),
                src_accesses: pass_type_write_accesses(src_pass.pass_type),
                dst_stages: pass_type_read_stages(dst_pass.pass_type),
                dst_accesses: pass_type_read_accesses(dst_pass.pass_type),
                old_layout: 0,
                new_layout: 0,
            }
        },
    ).filter(|ba: BarrierAction|
        exists|e: nat|
            #![trigger graph.edges[e as int]]
            e < graph.edges.len()
            && graph.edges[e as int].to_pass == pass_idx
            && graph.edges[e as int].resource == ba.resource
    )
}

//  ── Subpass Resource Tracking ───────────────────────────────────────────
//
//  Per-subpass resource state within a render pass.
//  Enables tracking which subpass reads/writes which resources.

///  Per-subpass resource state within a render pass.
pub struct SubpassResourceState {
    ///  Subpass index within the render pass.
    pub subpass_index: nat,
    ///  Resources read by this subpass.
    pub reads: Set<ResourceId>,
    ///  Resources written by this subpass.
    pub writes: Set<ResourceId>,
}

///  Decomposition of a render pass into subpasses with their dependencies.
pub struct PassSubpassDecomposition {
    ///  Per-subpass resource state.
    pub subpass_resources: Seq<SubpassResourceState>,
    ///  Subpass dependencies (indices into subpass_resources).
    pub subpass_deps: Seq<SubpassDepEdge>,
}

///  A dependency edge between two subpasses.
pub struct SubpassDepEdge {
    ///  Source subpass index.
    pub src_subpass: nat,
    ///  Destination subpass index.
    pub dst_subpass: nat,
    ///  Resource being transferred.
    pub resource: ResourceId,
    ///  Source stages.
    pub src_stages: PipelineStageFlags,
    ///  Destination stages.
    pub dst_stages: PipelineStageFlags,
}

///  A subpass decomposition is valid: all indices are in bounds
///  and the union of subpass reads/writes matches the pass reads/writes.
pub open spec fn subpass_decomposition_valid(
    decomp: PassSubpassDecomposition,
    pass: RenderPassNode,
) -> bool {
    //  Non-empty
    decomp.subpass_resources.len() > 0
    //  Subpass indices match their position
    && (forall|i: nat|
        #![trigger decomp.subpass_resources[i as int]]
        i < decomp.subpass_resources.len()
        ==> decomp.subpass_resources[i as int].subpass_index == i)
    //  Dependencies reference valid subpasses
    && (forall|d: nat|
        #![trigger decomp.subpass_deps[d as int]]
        d < decomp.subpass_deps.len()
        ==> decomp.subpass_deps[d as int].src_subpass < decomp.subpass_resources.len()
            && decomp.subpass_deps[d as int].dst_subpass < decomp.subpass_resources.len()
            && decomp.subpass_deps[d as int].src_subpass < decomp.subpass_deps[d as int].dst_subpass)
    //  Union of subpass reads covers pass reads
    && (forall|r: ResourceId|
        pass.reads.contains(r)
        ==> exists|i: nat|
            i < decomp.subpass_resources.len()
            && (#[trigger] decomp.subpass_resources[i as int]).reads.contains(r))
    //  Union of subpass writes covers pass writes
    && (forall|r: ResourceId|
        pass.writes.contains(r)
        ==> exists|i: nat|
            i < decomp.subpass_resources.len()
            && (#[trigger] decomp.subpass_resources[i as int]).writes.contains(r))
}

///  A subpass dependency covers a resource transfer within the pass.
pub open spec fn subpass_dep_covers(
    dep: SubpassDepEdge,
    decomp: PassSubpassDecomposition,
) -> bool {
    dep.src_subpass < decomp.subpass_resources.len()
    && dep.dst_subpass < decomp.subpass_resources.len()
    && decomp.subpass_resources[dep.src_subpass as int].writes.contains(dep.resource)
    && decomp.subpass_resources[dep.dst_subpass as int].reads.contains(dep.resource)
}

///  All intra-pass resource transfers are covered by subpass dependencies.
pub open spec fn intra_pass_deps_satisfied(
    decomp: PassSubpassDecomposition,
) -> bool {
    forall|src: nat, dst: nat, r: ResourceId|
        src < decomp.subpass_resources.len()
        && dst < decomp.subpass_resources.len()
        && src < dst
        && decomp.subpass_resources[src as int].writes.contains(r)
        && decomp.subpass_resources[dst as int].reads.contains(r)
        ==> exists|d: nat|
            #![trigger decomp.subpass_deps[d as int]]
            d < decomp.subpass_deps.len()
            && decomp.subpass_deps[d as int].resource == r
            && decomp.subpass_deps[d as int].src_subpass <= src
            && decomp.subpass_deps[d as int].dst_subpass >= dst
}

//  ── Proofs ──────────────────────────────────────────────────────────

///  A compiled graph with a valid execution order has
///  the same number of passes as the source graph.
pub proof fn lemma_compiled_order_length(cg: CompiledGraph)
    requires compiled_graph_well_formed(cg),
    ensures cg.execution_order.len() == cg.source_graph.passes.len(),
{
}

///  Barrier plans have one entry per pass.
pub proof fn lemma_barrier_plans_match_passes(cg: CompiledGraph)
    requires compiled_graph_well_formed(cg),
    ensures cg.barrier_plans.len() == cg.execution_order.len(),
{
}

///  Non-overlapping lifetimes allow safe memory reuse.
pub proof fn lemma_non_overlapping_lifetimes_aliasable(
    cg: CompiledGraph,
    r1: ResourceId,
    r2: ResourceId,
)
    requires
        cg.resource_lifetimes.contains_key(r1),
        cg.resource_lifetimes.contains_key(r2),
        lifetimes_non_overlapping(
            cg.resource_lifetimes[r1],
            cg.resource_lifetimes[r2],
        ),
    ensures memory_reuse_safe(cg, r1, r2),
{
}

///  Lifetimes that don't overlap are commutative.
pub proof fn lemma_lifetime_non_overlap_symmetric(
    lt1: ResourceLifetime,
    lt2: ResourceLifetime,
)
    requires lifetimes_non_overlapping(lt1, lt2),
    ensures lifetimes_non_overlapping(lt2, lt1),
{
}

///  A compiled graph with zero passes has zero barriers.
pub proof fn lemma_empty_graph_zero_barriers()
    ensures
        total_barrier_count(CompiledGraph {
            source_graph: RenderGraph {
                passes: Seq::empty(),
                edges: Seq::empty(),
            },
            execution_order: Seq::empty(),
            barrier_plans: Seq::empty(),
            resource_lifetimes: Map::empty(),
        }) == 0,
{
}

///  A well-formed compiled graph has all barrier plans well-formed.
pub proof fn lemma_compiled_all_plans_well_formed(
    cg: CompiledGraph,
    plan_idx: nat,
)
    requires
        compiled_graph_well_formed(cg),
        plan_idx < cg.barrier_plans.len(),
    ensures pass_barrier_plan_well_formed(
        cg.barrier_plans[plan_idx as int],
        cg.source_graph.passes.len(),
    ),
{
}

///  Well-formed compiled graph implies valid execution order.
pub proof fn lemma_compiled_has_valid_order(cg: CompiledGraph)
    requires compiled_graph_well_formed(cg),
    ensures execution_order_valid(cg.source_graph, cg.execution_order),
{
}

///  If lifetimes are valid and a resource is used at index i, the
///  lifetime contains i.
pub proof fn lemma_lifetime_contains_use(
    cg: CompiledGraph,
    r: ResourceId,
    i: nat,
)
    requires
        resource_lifetimes_valid(cg),
        cg.resource_lifetimes.contains_key(r),
        i < cg.execution_order.len(),
        cg.execution_order[i as int] < cg.source_graph.passes.len(),
        cg.source_graph.passes[cg.execution_order[i as int] as int].reads.contains(r)
            || cg.source_graph.passes[cg.execution_order[i as int] as int].writes.contains(r),
    ensures
        cg.resource_lifetimes[r].first_use <= i,
        i <= cg.resource_lifetimes[r].last_use,
{
}

///  Two resources with non-overlapping lifetimes are never used
///  in the same pass (useful for aliasing correctness).
pub proof fn lemma_non_overlapping_no_concurrent_use(
    cg: CompiledGraph,
    r1: ResourceId,
    r2: ResourceId,
    i: nat,
)
    requires
        resource_lifetimes_valid(cg),
        cg.resource_lifetimes.contains_key(r1),
        cg.resource_lifetimes.contains_key(r2),
        lifetimes_non_overlapping(
            cg.resource_lifetimes[r1],
            cg.resource_lifetimes[r2],
        ),
        i < cg.execution_order.len(),
        cg.execution_order[i as int] < cg.source_graph.passes.len(),
        cg.source_graph.passes[cg.execution_order[i as int] as int].reads.contains(r1)
            || cg.source_graph.passes[cg.execution_order[i as int] as int].writes.contains(r1),
    ensures
        !(cg.source_graph.passes[cg.execution_order[i as int] as int].reads.contains(r2)
            || cg.source_graph.passes[cg.execution_order[i as int] as int].writes.contains(r2)),
{
    //  r1 is used at i, so first_use(r1) <= i <= last_use(r1)
    //  By non-overlapping, r2's lifetime doesn't overlap r1's
    //  So i is outside r2's lifetime
    //  Since r2's lifetime covers all uses, r2 is not used at i
    let lt1 = cg.resource_lifetimes[r1];
    let lt2 = cg.resource_lifetimes[r2];
    assert(lt1.first_use <= i && i <= lt1.last_use);
    //  Non-overlapping: lt1.last_use < lt2.first_use || lt2.last_use < lt1.first_use
    //  Case 1: lt1.last_use < lt2.first_use => i <= lt1.last_use < lt2.first_use
    //          So i < lt2.first_use. If r2 were used at i, then lt2.first_use <= i. Contradiction.
    //  Case 2: lt2.last_use < lt1.first_use => lt2.last_use < lt1.first_use <= i
    //          So i > lt2.last_use. If r2 were used at i, then i <= lt2.last_use. Contradiction.
}

///  An empty barrier plan trivially covers deps for a pass with no incoming edges.
pub proof fn lemma_empty_plan_no_deps(
    graph: RenderGraph,
    pass_idx: nat,
)
    requires
        forall|e: nat|
            e < graph.edges.len()
            ==> graph.edges[e as int].to_pass != pass_idx,
    ensures barrier_plan_covers_deps(
        PassBarrierPlan {
            pass_index: pass_idx,
            pre_barriers: Seq::empty(),
            post_barriers: Seq::empty(),
        },
        graph,
        pass_idx,
    ),
{
}

///  Execution order indices are bounded.
pub proof fn lemma_execution_order_bounded(
    cg: CompiledGraph,
    i: nat,
)
    requires
        compiled_graph_well_formed(cg),
        i < cg.execution_order.len(),
    ensures
        cg.execution_order[i as int] < cg.source_graph.passes.len(),
{
}

///  A lifetime with first_use == last_use covers exactly one pass.
pub proof fn lemma_single_use_lifetime(
    lt: ResourceLifetime,
    graph: RenderGraph,
    order: Seq<nat>,
    r: ResourceId,
    i: nat,
)
    requires
        lt.first_use == lt.last_use,
        lt.first_use == i,
        lifetime_covers_uses(lt, graph, order, r),
        i < order.len(),
        order[i as int] < graph.passes.len(),
        graph.passes[order[i as int] as int].reads.contains(r)
            || graph.passes[order[i as int] as int].writes.contains(r),
    ensures
        //  No other pass uses r
        forall|j: nat|
            #![trigger order[j as int]]
            j < order.len()
            && j != i
            && order[j as int] < graph.passes.len()
            ==> !(graph.passes[order[j as int] as int].reads.contains(r)
                || graph.passes[order[j as int] as int].writes.contains(r)),
{
    assert forall|j: nat|
        j < order.len()
        && j != i
        && #[trigger] order[j as int] < graph.passes.len()
        implies !(graph.passes[order[j as int] as int].reads.contains(r)
            || graph.passes[order[j as int] as int].writes.contains(r)) by {
        if graph.passes[order[j as int] as int].reads.contains(r)
            || graph.passes[order[j as int] as int].writes.contains(r) {
            //  lifetime covers j => first_use <= j <= last_use
            //  But first_use == last_use == i, so j == i. Contradiction with j != i.
            assert(lt.first_use <= j && j <= lt.last_use);
            assert(j == i);
        }
    }
}

//  ── Extended Specs ──────────────────────────────────────────────────

///  A pass has a barrier for resource r in its pre-barriers.
pub open spec fn pass_has_pre_barrier(
    plan: PassBarrierPlan,
    r: ResourceId,
) -> bool {
    exists|b: nat|
        #![trigger plan.pre_barriers[b as int]]
        b < plan.pre_barriers.len()
        && plan.pre_barriers[b as int].resource == r
}

///  A pass has a barrier for resource r in its post-barriers.
pub open spec fn pass_has_post_barrier(
    plan: PassBarrierPlan,
    r: ResourceId,
) -> bool {
    exists|b: nat|
        #![trigger plan.post_barriers[b as int]]
        b < plan.post_barriers.len()
        && plan.post_barriers[b as int].resource == r
}

///  Total pre-barriers in a plan.
pub open spec fn plan_pre_barrier_count(plan: PassBarrierPlan) -> nat {
    plan.pre_barriers.len()
}

///  Total post-barriers in a plan.
pub open spec fn plan_post_barrier_count(plan: PassBarrierPlan) -> nat {
    plan.post_barriers.len()
}

///  Total barriers in a plan (pre + post).
pub open spec fn plan_total_barriers(plan: PassBarrierPlan) -> nat {
    plan.pre_barriers.len() + plan.post_barriers.len()
}

///  Execution order is a permutation (all values distinct).
pub open spec fn execution_order_permutation(order: Seq<nat>) -> bool {
    forall|i: nat, j: nat|
        #![trigger order[i as int], order[j as int]]
        i < order.len() && j < order.len() && i != j
        ==> order[i as int] != order[j as int]
}

///  Number of distinct resources used in the graph.
pub open spec fn graph_resource_count(graph: RenderGraph) -> nat {
    graph.edges.len()
}

///  A lifetime is valid (first_use <= last_use).
pub open spec fn lifetime_valid(lt: ResourceLifetime) -> bool {
    lt.first_use <= lt.last_use
}

///  A barrier action performs a layout transition.
pub open spec fn is_layout_transition(ba: BarrierAction) -> bool {
    ba.old_layout != ba.new_layout
}

///  A barrier action is an identity barrier (same layout).
pub open spec fn is_identity_barrier(ba: BarrierAction) -> bool {
    ba.old_layout == ba.new_layout
}

///  Memory reuse is safe symmetrically.
pub open spec fn memory_reuse_safe_symmetric(
    cg: CompiledGraph,
    r1: ResourceId,
    r2: ResourceId,
) -> bool {
    memory_reuse_safe(cg, r1, r2) && memory_reuse_safe(cg, r2, r1)
}

///  A compiled graph has no barriers (empty barrier plans).
pub open spec fn has_no_barriers(cg: CompiledGraph) -> bool {
    forall|i: nat|
        #![trigger cg.barrier_plans[i as int]]
        i < cg.barrier_plans.len()
        ==> cg.barrier_plans[i as int].pre_barriers.len() == 0
            && cg.barrier_plans[i as int].post_barriers.len() == 0
}

///  A resource is read-only through the graph (never written).
pub open spec fn resource_read_only(
    graph: RenderGraph,
    order: Seq<nat>,
    r: ResourceId,
) -> bool {
    forall|i: nat|
        #![trigger order[i as int]]
        i < order.len()
        && order[i as int] < graph.passes.len()
        ==> !graph.passes[order[i as int] as int].writes.contains(r)
}

///  A resource is write-only through the graph (never read).
pub open spec fn resource_write_only(
    graph: RenderGraph,
    order: Seq<nat>,
    r: ResourceId,
) -> bool {
    forall|i: nat|
        #![trigger order[i as int]]
        i < order.len()
        && order[i as int] < graph.passes.len()
        ==> !graph.passes[order[i as int] as int].reads.contains(r)
}

//  ── Extended Proofs ────────────────────────────────────────────────

///  Memory reuse safety is symmetric.
pub proof fn lemma_memory_reuse_safe_symmetric(
    cg: CompiledGraph,
    r1: ResourceId,
    r2: ResourceId,
)
    requires memory_reuse_safe(cg, r1, r2),
    ensures memory_reuse_safe(cg, r2, r1),
{
    lemma_lifetime_non_overlap_symmetric(
        cg.resource_lifetimes[r1],
        cg.resource_lifetimes[r2],
    );
}

///  An empty barrier plan has zero total barriers.
pub proof fn lemma_empty_plan_zero_barriers(pass_idx: nat)
    ensures plan_total_barriers(PassBarrierPlan {
        pass_index: pass_idx,
        pre_barriers: Seq::empty(),
        post_barriers: Seq::empty(),
    }) == 0,
{
}

///  A valid lifetime has first_use <= last_use.
pub proof fn lemma_valid_lifetime_ordered(
    cg: CompiledGraph,
    r: ResourceId,
    i: nat,
    j: nat,
)
    requires
        resource_lifetimes_valid(cg),
        cg.resource_lifetimes.contains_key(r),
        i < cg.execution_order.len(),
        j < cg.execution_order.len(),
        cg.execution_order[i as int] < cg.source_graph.passes.len(),
        cg.execution_order[j as int] < cg.source_graph.passes.len(),
        cg.source_graph.passes[cg.execution_order[i as int] as int].reads.contains(r)
            || cg.source_graph.passes[cg.execution_order[i as int] as int].writes.contains(r),
        cg.source_graph.passes[cg.execution_order[j as int] as int].reads.contains(r)
            || cg.source_graph.passes[cg.execution_order[j as int] as int].writes.contains(r),
    ensures
        cg.resource_lifetimes[r].first_use <= cg.resource_lifetimes[r].last_use,
{
    let lt = cg.resource_lifetimes[r];
    assert(lt.first_use <= i && i <= lt.last_use);
}

///  Plan total barriers is sum of pre and post.
pub proof fn lemma_plan_total_is_sum(plan: PassBarrierPlan)
    ensures plan_total_barriers(plan)
        == plan_pre_barrier_count(plan) + plan_post_barrier_count(plan),
{
}

///  A read-only resource needs no write barriers.
pub proof fn lemma_read_only_no_writes(
    graph: RenderGraph,
    order: Seq<nat>,
    r: ResourceId,
    i: nat,
)
    requires
        resource_read_only(graph, order, r),
        i < order.len(),
        order[i as int] < graph.passes.len(),
    ensures
        !graph.passes[order[i as int] as int].writes.contains(r),
{
}

///  A graph with no barriers has zero total barrier count.
pub proof fn lemma_no_barriers_zero_total(cg: CompiledGraph)
    requires has_no_barriers(cg),
    ensures total_barrier_count(cg) == 0,
    decreases cg.barrier_plans.len(),
{
    if cg.barrier_plans.len() > 0 {
        let last = cg.barrier_plans[cg.barrier_plans.len() - 1];
        assert(last.pre_barriers.len() == 0);
        assert(last.post_barriers.len() == 0);
        let sub_cg = CompiledGraph {
            barrier_plans: cg.barrier_plans.subrange(0, cg.barrier_plans.len() as int - 1),
            ..cg
        };
        assert forall|i: nat|
            #[trigger] sub_cg.barrier_plans[i as int] == sub_cg.barrier_plans[i as int]
            && i < sub_cg.barrier_plans.len()
            implies
                sub_cg.barrier_plans[i as int].pre_barriers.len() == 0
                && sub_cg.barrier_plans[i as int].post_barriers.len() == 0
        by {
            assert(sub_cg.barrier_plans[i as int] == cg.barrier_plans[i as int]);
        }
        lemma_no_barriers_zero_total(sub_cg);
    }
}

///  Layout transition implies barrier is not identity.
pub proof fn lemma_layout_transition_not_identity(ba: BarrierAction)
    requires is_layout_transition(ba),
    ensures !is_identity_barrier(ba),
{
}

///  Identity barrier implies no layout transition.
pub proof fn lemma_identity_no_layout_transition(ba: BarrierAction)
    requires is_identity_barrier(ba),
    ensures !is_layout_transition(ba),
{
}

///  A pass with a pre-barrier for r has a non-empty pre-barrier list.
pub proof fn lemma_pre_barrier_implies_nonempty(
    plan: PassBarrierPlan,
    r: ResourceId,
)
    requires pass_has_pre_barrier(plan, r),
    ensures plan.pre_barriers.len() > 0,
{
}

///  A pass with a post-barrier for r has a non-empty post-barrier list.
pub proof fn lemma_post_barrier_implies_nonempty(
    plan: PassBarrierPlan,
    r: ResourceId,
)
    requires pass_has_post_barrier(plan, r),
    ensures plan.post_barriers.len() > 0,
{
}

//  ── Subpass Proofs ────────────────────────────────────────────────

///  A single-subpass decomposition is trivially valid if it matches the pass.
pub proof fn lemma_single_subpass_valid(
    pass: RenderPassNode,
)
    ensures subpass_decomposition_valid(
        PassSubpassDecomposition {
            subpass_resources: seq![SubpassResourceState {
                subpass_index: 0,
                reads: pass.reads,
                writes: pass.writes,
            }],
            subpass_deps: Seq::empty(),
        },
        pass,
    ),
{
    let decomp = PassSubpassDecomposition {
        subpass_resources: seq![SubpassResourceState {
            subpass_index: 0,
            reads: pass.reads,
            writes: pass.writes,
        }],
        subpass_deps: Seq::empty(),
    };
    //  Non-empty
    assert(decomp.subpass_resources.len() > 0);
    //  Subpass indices match position
    assert(decomp.subpass_resources[0].subpass_index == 0);
    //  Reads covered
    assert forall|r: ResourceId|
        pass.reads.contains(r)
        implies exists|i: nat|
            i < decomp.subpass_resources.len()
            && (#[trigger] decomp.subpass_resources[i as int]).reads.contains(r) by {
        assert(decomp.subpass_resources[0].reads.contains(r));
    }
    //  Writes covered
    assert forall|r: ResourceId|
        pass.writes.contains(r)
        implies exists|i: nat|
            i < decomp.subpass_resources.len()
            && (#[trigger] decomp.subpass_resources[i as int]).writes.contains(r) by {
        assert(decomp.subpass_resources[0].writes.contains(r));
    }
}

///  A single-subpass decomposition has trivially satisfied intra-pass deps
///  (no subpass pairs with src < dst).
pub proof fn lemma_single_subpass_deps_trivial(
    pass: RenderPassNode,
)
    ensures intra_pass_deps_satisfied(
        PassSubpassDecomposition {
            subpass_resources: seq![SubpassResourceState {
                subpass_index: 0,
                reads: pass.reads,
                writes: pass.writes,
            }],
            subpass_deps: Seq::empty(),
        },
    ),
{
}

///  Pass-level barriers imply write stages/accesses are non-empty for proper pass types.
pub proof fn lemma_pass_type_write_stages_nonempty(pt: PassType)
    ensures !pass_type_write_stages(pt).stages.is_empty(),
{
    match pt {
        PassType::Graphics => {
            assert(pass_type_write_stages(pt).stages.contains(STAGE_COLOR_ATTACHMENT_OUTPUT()));
        },
        PassType::Compute => {
            assert(pass_type_write_stages(pt).stages.contains(STAGE_COMPUTE_SHADER()));
        },
        PassType::Transfer => {
            assert(pass_type_write_stages(pt).stages.contains(STAGE_TRANSFER()));
        },
    }
}

///  Pass-level barriers imply read stages/accesses are non-empty for proper pass types.
pub proof fn lemma_pass_type_read_stages_nonempty(pt: PassType)
    ensures !pass_type_read_stages(pt).stages.is_empty(),
{
    match pt {
        PassType::Graphics => {
            assert(pass_type_read_stages(pt).stages.contains(STAGE_FRAGMENT_SHADER()));
        },
        PassType::Compute => {
            assert(pass_type_read_stages(pt).stages.contains(STAGE_COMPUTE_SHADER()));
        },
        PassType::Transfer => {
            assert(pass_type_read_stages(pt).stages.contains(STAGE_TRANSFER()));
        },
    }
}

} //  verus!
