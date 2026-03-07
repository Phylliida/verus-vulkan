use vstd::prelude::*;
use crate::flags::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// Extended subpass dependency that supports self-dependencies.
///
/// In Vulkan, a self-dependency (src_subpass == dst_subpass) is valid
/// when the BY_REGION bit is set. This enables tile-based deferred
/// rendering (TBDR) optimizations on mobile GPUs where a subpass
/// reads its own output within the same tile.
pub struct ExtendedSubpassDependency {
    pub src_subpass: nat,
    pub dst_subpass: nat,
    /// Whether the dependency is framebuffer-local (BY_REGION).
    pub by_region: bool,
    /// Source pipeline stages.
    pub src_stage_mask: PipelineStageFlags,
    /// Destination pipeline stages.
    pub dst_stage_mask: PipelineStageFlags,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// A self-dependency: source and destination are the same subpass.
pub open spec fn is_self_dependency(dep: ExtendedSubpassDependency) -> bool {
    dep.src_subpass == dep.dst_subpass
}

/// A self-dependency is valid only with BY_REGION flag.
pub open spec fn self_dependency_valid(dep: ExtendedSubpassDependency) -> bool {
    is_self_dependency(dep) ==> dep.by_region
}

/// Extended dependency is well-formed within a render pass.
pub open spec fn extended_dependency_well_formed(
    dep: ExtendedSubpassDependency,
    subpass_count: nat,
) -> bool {
    dep.src_subpass < subpass_count
    && dep.dst_subpass < subpass_count
    // Non-self dependencies must have src before dst
    && (!is_self_dependency(dep) ==> dep.src_subpass < dep.dst_subpass)
    // Self-dependencies must have BY_REGION
    && self_dependency_valid(dep)
}

/// All extended dependencies in a render pass are well-formed.
pub open spec fn all_extended_deps_well_formed(
    deps: Seq<ExtendedSubpassDependency>,
    subpass_count: nat,
) -> bool {
    forall|i: int| 0 <= i < deps.len() ==>
        extended_dependency_well_formed(#[trigger] deps[i], subpass_count)
}

/// A self-dependency barrier is needed at a subpass if there is a
/// self-dependency declared for that subpass.
pub open spec fn has_self_dependency(
    deps: Seq<ExtendedSubpassDependency>,
    subpass_idx: nat,
) -> bool {
    exists|i: int| 0 <= i < deps.len()
        && (#[trigger] deps[i]).src_subpass == subpass_idx
        && deps[i].dst_subpass == subpass_idx
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// A self-dependency with BY_REGION is valid.
pub proof fn lemma_self_dep_with_by_region_valid(
    dep: ExtendedSubpassDependency,
)
    requires
        is_self_dependency(dep),
        dep.by_region,
    ensures
        self_dependency_valid(dep),
{
}

/// A non-self dependency has src < dst when well-formed.
pub proof fn lemma_non_self_dep_ordered(
    dep: ExtendedSubpassDependency,
    subpass_count: nat,
)
    requires
        extended_dependency_well_formed(dep, subpass_count),
        !is_self_dependency(dep),
    ensures
        dep.src_subpass < dep.dst_subpass,
        dep.src_subpass < subpass_count,
        dep.dst_subpass < subpass_count,
{
}

/// Empty dependency list is trivially well-formed.
pub proof fn lemma_empty_deps_well_formed(subpass_count: nat)
    ensures all_extended_deps_well_formed(Seq::empty(), subpass_count),
{
}

/// If there is no self-dependency for a subpass, the subpass does not
/// need a mid-subpass barrier.
pub proof fn lemma_no_self_dep_no_barrier(
    deps: Seq<ExtendedSubpassDependency>,
    subpass_idx: nat,
)
    requires
        !has_self_dependency(deps, subpass_idx),
    ensures
        forall|i: int| 0 <= i < deps.len()
            ==> !(deps[i].src_subpass == subpass_idx && deps[i].dst_subpass == subpass_idx),
{
}

/// A self-dependency implies BY_REGION when all deps are well-formed.
pub proof fn lemma_self_dep_implies_by_region(
    deps: Seq<ExtendedSubpassDependency>,
    subpass_count: nat,
    subpass_idx: nat,
    k: int,
)
    requires
        all_extended_deps_well_formed(deps, subpass_count),
        0 <= k < deps.len(),
        deps[k].src_subpass == subpass_idx,
        deps[k].dst_subpass == subpass_idx,
    ensures
        deps[k].by_region,
{
    assert(extended_dependency_well_formed(deps[k], subpass_count));
    assert(is_self_dependency(deps[k]));
    assert(self_dependency_valid(deps[k]));
}

/// A well-formed extended dependency with src != dst is a valid
/// original-style dependency (src < dst).
pub proof fn lemma_extended_backwards_compatible(
    dep: ExtendedSubpassDependency,
    subpass_count: nat,
)
    requires
        extended_dependency_well_formed(dep, subpass_count),
        dep.src_subpass != dep.dst_subpass,
    ensures
        dep.src_subpass < dep.dst_subpass,
{
}

/// A single-subpass render pass cannot have non-self dependencies.
pub proof fn lemma_single_subpass_only_self_deps(
    dep: ExtendedSubpassDependency,
)
    requires
        extended_dependency_well_formed(dep, 1),
    ensures
        is_self_dependency(dep),
        dep.by_region,
{
    // src < 1 and dst < 1 means both are 0
    assert(dep.src_subpass == 0);
    assert(dep.dst_subpass == 0);
}

} // verus!
