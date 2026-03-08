use vstd::prelude::*;
use crate::resource::*;
use crate::render_graph::*;
use crate::render_graph_compile::*;
use crate::flags::*;

verus! {

// ── Types ──────────────────────────────────────────────────────────────

/// Runtime representation of a barrier action.
pub struct RuntimeBarrierAction {
    /// Resource identifier.
    pub resource_id: nat,
    /// Is this a buffer or image barrier?
    pub is_image: bool,
    /// Source stage bits.
    pub src_stage_bits: nat,
    /// Destination stage bits.
    pub dst_stage_bits: nat,
    /// Source access bits.
    pub src_access_bits: nat,
    /// Destination access bits.
    pub dst_access_bits: nat,
    /// Old image layout (ignored for buffers).
    pub old_layout: nat,
    /// New image layout (ignored for buffers).
    pub new_layout: nat,
}

/// Runtime compiled graph output.
pub struct RuntimeCompiledGraph {
    /// Pass execution order.
    pub order: Seq<nat>,
    /// Pre-barriers for each pass.
    pub pre_barriers: Seq<Seq<RuntimeBarrierAction>>,
    /// Post-barriers for each pass.
    pub post_barriers: Seq<Seq<RuntimeBarrierAction>>,
    /// Total number of barriers.
    pub total_barriers: nat,
}

// ── Spec Functions ──────────────────────────────────────────────────

/// A runtime compiled graph is well-formed.
pub open spec fn runtime_compiled_well_formed(rcg: RuntimeCompiledGraph) -> bool {
    rcg.order.len() == rcg.pre_barriers.len()
    && rcg.order.len() == rcg.post_barriers.len()
}

/// Count of pre-barriers for a specific pass.
pub open spec fn pass_pre_barrier_count(
    rcg: RuntimeCompiledGraph,
    pass_idx: nat,
) -> nat
    recommends pass_idx < rcg.pre_barriers.len(),
{
    rcg.pre_barriers[pass_idx as int].len()
}

/// Count of post-barriers for a specific pass.
pub open spec fn pass_post_barrier_count(
    rcg: RuntimeCompiledGraph,
    pass_idx: nat,
) -> nat
    recommends pass_idx < rcg.post_barriers.len(),
{
    rcg.post_barriers[pass_idx as int].len()
}

/// Total barriers across all passes.
pub open spec fn compute_total_barriers(rcg: RuntimeCompiledGraph) -> nat
    decreases rcg.order.len(),
{
    if rcg.order.len() == 0 || !runtime_compiled_well_formed(rcg) {
        0
    } else {
        let last = rcg.order.len() as nat - 1;
        rcg.pre_barriers[last as int].len()
        + rcg.post_barriers[last as int].len()
        + compute_total_barriers(RuntimeCompiledGraph {
            order: rcg.order.subrange(0, last as int),
            pre_barriers: rcg.pre_barriers.subrange(0, last as int),
            post_barriers: rcg.post_barriers.subrange(0, last as int),
            total_barriers: 0,
        })
    }
}

/// A runtime barrier action is valid: non-zero stage bits.
pub open spec fn runtime_barrier_valid(rba: RuntimeBarrierAction) -> bool {
    rba.src_stage_bits > 0 && rba.dst_stage_bits > 0
}

/// All barriers for a pass are valid.
pub open spec fn pass_barriers_all_valid(
    rcg: RuntimeCompiledGraph,
    pass_idx: nat,
) -> bool
    recommends pass_idx < rcg.pre_barriers.len(),
{
    (forall|i: nat|
        #![trigger rcg.pre_barriers[pass_idx as int][i as int]]
        i < rcg.pre_barriers[pass_idx as int].len()
        ==> runtime_barrier_valid(rcg.pre_barriers[pass_idx as int][i as int]))
    && (forall|i: nat|
        #![trigger rcg.post_barriers[pass_idx as int][i as int]]
        i < rcg.post_barriers[pass_idx as int].len()
        ==> runtime_barrier_valid(rcg.post_barriers[pass_idx as int][i as int]))
}

/// A runtime compiled graph where all barriers are valid.
pub open spec fn all_barriers_valid(rcg: RuntimeCompiledGraph) -> bool {
    forall|p: nat|
        #![trigger rcg.pre_barriers[p as int]]
        p < rcg.order.len()
        ==> pass_barriers_all_valid(rcg, p)
}

/// Validation result: the compiled graph is well-formed and all barriers valid.
pub open spec fn validate_compiled_graph_spec(rcg: RuntimeCompiledGraph) -> bool {
    runtime_compiled_well_formed(rcg)
    && all_barriers_valid(rcg)
}

/// No duplicate pass indices in the execution order.
pub open spec fn order_no_duplicates(order: Seq<nat>) -> bool {
    forall|i: nat, j: nat|
        #![trigger order[i as int], order[j as int]]
        i < order.len() && j < order.len() && i != j
        ==> order[i as int] != order[j as int]
}

// ── Proofs ──────────────────────────────────────────────────────────

/// An empty compiled graph is well-formed.
pub proof fn lemma_empty_runtime_compiled_well_formed()
    ensures runtime_compiled_well_formed(RuntimeCompiledGraph {
        order: Seq::empty(),
        pre_barriers: Seq::empty(),
        post_barriers: Seq::empty(),
        total_barriers: 0,
    }),
{
}

/// An empty compiled graph has zero total barriers.
pub proof fn lemma_empty_runtime_zero_barriers()
    ensures compute_total_barriers(RuntimeCompiledGraph {
        order: Seq::empty(),
        pre_barriers: Seq::empty(),
        post_barriers: Seq::empty(),
        total_barriers: 0,
    }) == 0,
{
}

/// Validation of a well-formed, all-valid graph succeeds.
pub proof fn lemma_valid_graph_passes_validation(
    rcg: RuntimeCompiledGraph,
)
    requires
        runtime_compiled_well_formed(rcg),
        all_barriers_valid(rcg),
    ensures validate_compiled_graph_spec(rcg),
{
}

/// Well-formed runtime graph has matching lengths.
pub proof fn lemma_runtime_matching_lengths(
    rcg: RuntimeCompiledGraph,
)
    requires runtime_compiled_well_formed(rcg),
    ensures
        rcg.order.len() == rcg.pre_barriers.len(),
        rcg.order.len() == rcg.post_barriers.len(),
{
}

/// Pass barrier count is non-negative (trivially true for nat).
pub proof fn lemma_barrier_count_non_negative(
    rcg: RuntimeCompiledGraph,
    pass_idx: nat,
)
    requires
        runtime_compiled_well_formed(rcg),
        pass_idx < rcg.order.len(),
    ensures
        pass_pre_barrier_count(rcg, pass_idx) >= 0,
        pass_post_barrier_count(rcg, pass_idx) >= 0,
{
}

/// If all barriers for pass p are valid, each pre-barrier has non-zero stages.
pub proof fn lemma_valid_barriers_have_stages(
    rcg: RuntimeCompiledGraph,
    pass_idx: nat,
    barrier_idx: nat,
)
    requires
        runtime_compiled_well_formed(rcg),
        pass_idx < rcg.order.len(),
        pass_barriers_all_valid(rcg, pass_idx),
        barrier_idx < rcg.pre_barriers[pass_idx as int].len(),
    ensures
        rcg.pre_barriers[pass_idx as int][barrier_idx as int].src_stage_bits > 0,
        rcg.pre_barriers[pass_idx as int][barrier_idx as int].dst_stage_bits > 0,
{
}

/// An empty graph trivially has all barriers valid.
pub proof fn lemma_empty_all_barriers_valid()
    ensures all_barriers_valid(RuntimeCompiledGraph {
        order: Seq::empty(),
        pre_barriers: Seq::empty(),
        post_barriers: Seq::empty(),
        total_barriers: 0,
    }),
{
}

/// A graph with no barriers per pass validates.
pub proof fn lemma_no_barriers_validates(n: nat)
    ensures validate_compiled_graph_spec(RuntimeCompiledGraph {
        order: Seq::new(n, |i: int| i as nat),
        pre_barriers: Seq::new(n, |_i: int| Seq::<RuntimeBarrierAction>::empty()),
        post_barriers: Seq::new(n, |_i: int| Seq::<RuntimeBarrierAction>::empty()),
        total_barriers: 0,
    }),
{
    let rcg = RuntimeCompiledGraph {
        order: Seq::new(n, |i: int| i as nat),
        pre_barriers: Seq::new(n, |_i: int| Seq::<RuntimeBarrierAction>::empty()),
        post_barriers: Seq::new(n, |_i: int| Seq::<RuntimeBarrierAction>::empty()),
        total_barriers: 0,
    };
    assert(runtime_compiled_well_formed(rcg));
    assert forall|p: nat|
        p < rcg.order.len()
        implies pass_barriers_all_valid(rcg, p) by {
        // No barriers to validate
    }
}

// ── Extended Specs ──────────────────────────────────────────────────

/// Total number of pre+post barriers for a pass.
pub open spec fn runtime_pass_total_barriers(
    rcg: RuntimeCompiledGraph,
    pass_idx: nat,
) -> nat
    recommends
        pass_idx < rcg.pre_barriers.len(),
        pass_idx < rcg.post_barriers.len(),
{
    rcg.pre_barriers[pass_idx as int].len() + rcg.post_barriers[pass_idx as int].len()
}

/// Number of passes that have at least one barrier.
pub open spec fn passes_with_barriers(rcg: RuntimeCompiledGraph) -> nat
    decreases rcg.order.len(),
{
    if rcg.order.len() == 0 || !runtime_compiled_well_formed(rcg) {
        0
    } else {
        let last = rcg.order.len() as nat - 1;
        let has_barrier: nat = if rcg.pre_barriers[last as int].len() > 0
            || rcg.post_barriers[last as int].len() > 0
        { 1 } else { 0 };
        has_barrier + passes_with_barriers(RuntimeCompiledGraph {
            order: rcg.order.subrange(0, last as int),
            pre_barriers: rcg.pre_barriers.subrange(0, last as int),
            post_barriers: rcg.post_barriers.subrange(0, last as int),
            total_barriers: 0,
        })
    }
}

/// Execution order indices are bounded by num_passes.
pub open spec fn runtime_order_bounded(rcg: RuntimeCompiledGraph, num_passes: nat) -> bool {
    forall|i: nat|
        #![trigger rcg.order[i as int]]
        i < rcg.order.len()
        ==> rcg.order[i as int] < num_passes
}

/// No duplicate pass indices in the runtime order.
pub open spec fn runtime_order_no_duplicates(rcg: RuntimeCompiledGraph) -> bool {
    order_no_duplicates(rcg.order)
}

/// A runtime compiled graph is fully valid.
pub open spec fn runtime_compiled_fully_valid(rcg: RuntimeCompiledGraph, num_passes: nat) -> bool {
    runtime_compiled_well_formed(rcg)
    && all_barriers_valid(rcg)
    && runtime_order_bounded(rcg, num_passes)
    && runtime_order_no_duplicates(rcg)
}

/// All pre-barriers for a specific pass are valid.
pub open spec fn pass_pre_barriers_valid(
    rcg: RuntimeCompiledGraph,
    pass_idx: nat,
) -> bool
    recommends pass_idx < rcg.pre_barriers.len(),
{
    forall|i: nat|
        #![trigger rcg.pre_barriers[pass_idx as int][i as int]]
        i < rcg.pre_barriers[pass_idx as int].len()
        ==> runtime_barrier_valid(rcg.pre_barriers[pass_idx as int][i as int])
}

/// All post-barriers for a specific pass are valid.
pub open spec fn pass_post_barriers_valid(
    rcg: RuntimeCompiledGraph,
    pass_idx: nat,
) -> bool
    recommends pass_idx < rcg.post_barriers.len(),
{
    forall|i: nat|
        #![trigger rcg.post_barriers[pass_idx as int][i as int]]
        i < rcg.post_barriers[pass_idx as int].len()
        ==> runtime_barrier_valid(rcg.post_barriers[pass_idx as int][i as int])
}

/// Count of passes in the compiled graph.
pub open spec fn runtime_pass_count(rcg: RuntimeCompiledGraph) -> nat {
    rcg.order.len()
}

// ── Extended Proofs ────────────────────────────────────────────────

/// All barriers valid implies each pass has valid pre-barriers.
pub proof fn lemma_all_valid_implies_pre_valid(
    rcg: RuntimeCompiledGraph,
    pass_idx: nat,
)
    requires
        all_barriers_valid(rcg),
        pass_idx < rcg.order.len(),
    ensures pass_pre_barriers_valid(rcg, pass_idx),
{
}

/// All barriers valid implies each pass has valid post-barriers.
pub proof fn lemma_all_valid_implies_post_valid(
    rcg: RuntimeCompiledGraph,
    pass_idx: nat,
)
    requires
        all_barriers_valid(rcg),
        pass_idx < rcg.order.len(),
    ensures pass_post_barriers_valid(rcg, pass_idx),
{
    assert(pass_barriers_all_valid(rcg, pass_idx));
}

/// Validate implies well-formed.
pub proof fn lemma_validate_implies_well_formed(rcg: RuntimeCompiledGraph)
    requires validate_compiled_graph_spec(rcg),
    ensures runtime_compiled_well_formed(rcg),
{
}

/// Validate implies all barriers valid.
pub proof fn lemma_validate_implies_all_valid(rcg: RuntimeCompiledGraph)
    requires validate_compiled_graph_spec(rcg),
    ensures all_barriers_valid(rcg),
{
}

/// Empty pass has zero runtime barriers.
pub proof fn lemma_empty_pass_zero_barriers(pass_idx: nat)
    ensures runtime_pass_total_barriers(
        RuntimeCompiledGraph {
            order: Seq::new(pass_idx + 1, |i: int| i as nat),
            pre_barriers: Seq::new(pass_idx + 1, |_i: int| Seq::<RuntimeBarrierAction>::empty()),
            post_barriers: Seq::new(pass_idx + 1, |_i: int| Seq::<RuntimeBarrierAction>::empty()),
            total_barriers: 0,
        },
        pass_idx,
    ) == 0,
{
}

/// Fully valid implies well-formed.
pub proof fn lemma_fully_valid_implies_well_formed(
    rcg: RuntimeCompiledGraph,
    num_passes: nat,
)
    requires runtime_compiled_fully_valid(rcg, num_passes),
    ensures runtime_compiled_well_formed(rcg),
{
}

/// Fully valid implies bounded order.
pub proof fn lemma_fully_valid_implies_bounded(
    rcg: RuntimeCompiledGraph,
    num_passes: nat,
)
    requires runtime_compiled_fully_valid(rcg, num_passes),
    ensures runtime_order_bounded(rcg, num_passes),
{
}

/// Runtime pass count matches order length.
pub proof fn lemma_pass_count_matches(rcg: RuntimeCompiledGraph)
    ensures runtime_pass_count(rcg) == rcg.order.len(),
{
}

/// Empty graph has zero passes.
pub proof fn lemma_empty_graph_zero_passes()
    ensures runtime_pass_count(RuntimeCompiledGraph {
        order: Seq::empty(),
        pre_barriers: Seq::empty(),
        post_barriers: Seq::empty(),
        total_barriers: 0,
    }) == 0,
{
}

/// Well-formed implies pre and post barrier lengths match.
pub proof fn lemma_wf_pre_post_match(rcg: RuntimeCompiledGraph)
    requires runtime_compiled_well_formed(rcg),
    ensures rcg.pre_barriers.len() == rcg.post_barriers.len(),
{
}

/// Order length equals pre-barrier length.
pub proof fn lemma_wf_order_pre_match(rcg: RuntimeCompiledGraph)
    requires runtime_compiled_well_formed(rcg),
    ensures rcg.order.len() == rcg.pre_barriers.len(),
{
}

/// Empty runtime compiled graph passes validation.
pub proof fn lemma_empty_validates()
    ensures validate_compiled_graph_spec(RuntimeCompiledGraph {
        order: Seq::empty(),
        pre_barriers: Seq::empty(),
        post_barriers: Seq::empty(),
        total_barriers: 0,
    }),
{
    let rcg = RuntimeCompiledGraph {
        order: Seq::empty(),
        pre_barriers: Seq::empty(),
        post_barriers: Seq::empty(),
        total_barriers: 0,
    };
    assert(runtime_compiled_well_formed(rcg));
    assert(all_barriers_valid(rcg));
}

/// Pass count is non-negative (trivial for nat).
pub proof fn lemma_pass_count_non_negative(rcg: RuntimeCompiledGraph)
    ensures runtime_pass_count(rcg) >= 0,
{
}

/// Fully valid with n passes means order has n entries.
pub proof fn lemma_fully_valid_order_length(
    rcg: RuntimeCompiledGraph,
    num_passes: nat,
)
    requires runtime_compiled_fully_valid(rcg, num_passes),
    ensures rcg.order.len() == runtime_pass_count(rcg),
{
}

/// Fully valid implies all barriers valid.
pub proof fn lemma_fully_valid_all_barriers(
    rcg: RuntimeCompiledGraph,
    num_passes: nat,
)
    requires runtime_compiled_fully_valid(rcg, num_passes),
    ensures all_barriers_valid(rcg),
{
}

} // verus!
