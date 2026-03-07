use vstd::prelude::*;
use crate::descriptor::*;
use crate::shader_interface::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// Ghost state for a Vulkan pipeline layout (VkPipelineLayout).
///
/// A pipeline layout defines the interface between shader stages and
/// shader resources. It specifies which descriptor set layouts and
/// push constant ranges the pipeline uses.
pub struct PipelineLayoutState {
    pub id: nat,
    /// Descriptor set layouts, indexed by set number.
    pub set_layouts: Seq<nat>,
    /// Push constant ranges declared by this layout.
    pub push_constant_ranges: Seq<PushConstantRange>,
    pub alive: bool,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// Two pipeline layouts are compatible for a given set index:
/// all set layouts at indices <= set_index match.
pub open spec fn layouts_compatible_at_set(
    layout_a: PipelineLayoutState,
    layout_b: PipelineLayoutState,
    set_index: nat,
) -> bool {
    set_index < layout_a.set_layouts.len()
    && set_index < layout_b.set_layouts.len()
    && (forall|i: int| 0 <= i <= set_index as int ==>
        (#[trigger] layout_a.set_layouts[i]) == layout_b.set_layouts[i])
}

/// Two pipeline layouts are fully compatible: same set layouts and
/// same push constant ranges.
pub open spec fn layouts_fully_compatible(
    layout_a: PipelineLayoutState,
    layout_b: PipelineLayoutState,
) -> bool {
    layout_a.set_layouts =~= layout_b.set_layouts
    && layout_a.push_constant_ranges =~= layout_b.push_constant_ranges
}

/// Push constant ranges don't overlap in a layout.
pub open spec fn push_constant_ranges_non_overlapping(
    ranges: Seq<PushConstantRange>,
) -> bool {
    forall|i: int, j: int|
        0 <= i < ranges.len() && 0 <= j < ranges.len() && i != j
        ==> !push_constant_ranges_overlap(
            (#[trigger] ranges[i]),
            (#[trigger] ranges[j]),
        )
}

/// Two push constant ranges overlap.
pub open spec fn push_constant_ranges_overlap(
    a: PushConstantRange,
    b: PushConstantRange,
) -> bool {
    a.offset < b.offset + b.size
    && b.offset < a.offset + a.size
}

/// A pipeline layout is well-formed.
pub open spec fn pipeline_layout_well_formed(
    layout: PipelineLayoutState,
) -> bool {
    layout.alive
    && push_constant_ranges_non_overlapping(layout.push_constant_ranges)
}

/// A descriptor set is compatible with a pipeline layout at a given set index.
pub open spec fn descriptor_set_compatible_with_layout(
    set: DescriptorSetState,
    layout: PipelineLayoutState,
    set_index: nat,
) -> bool {
    set_index < layout.set_layouts.len()
    && set.layout_id == layout.set_layouts[set_index as int]
}

/// Total push constant size across all ranges.
pub open spec fn total_push_constant_size(
    ranges: Seq<PushConstantRange>,
) -> nat
    decreases ranges.len(),
{
    if ranges.len() == 0 {
        0
    } else {
        let last = ranges.last();
        total_push_constant_size(ranges.drop_last()) + last.size
    }
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// Full layout compatibility implies compatibility at every set index.
pub proof fn lemma_full_compat_implies_set_compat(
    layout_a: PipelineLayoutState,
    layout_b: PipelineLayoutState,
    set_index: nat,
)
    requires
        layouts_fully_compatible(layout_a, layout_b),
        set_index < layout_a.set_layouts.len(),
    ensures
        layouts_compatible_at_set(layout_a, layout_b, set_index),
{
}

/// Layout compatibility is reflexive.
pub proof fn lemma_layout_compat_reflexive(
    layout: PipelineLayoutState,
)
    ensures layouts_fully_compatible(layout, layout),
{
}

/// Layout compatibility is symmetric.
pub proof fn lemma_layout_compat_symmetric(
    layout_a: PipelineLayoutState,
    layout_b: PipelineLayoutState,
)
    requires layouts_fully_compatible(layout_a, layout_b),
    ensures layouts_fully_compatible(layout_b, layout_a),
{
}

/// A layout with no push constant ranges has non-overlapping ranges trivially.
pub proof fn lemma_empty_push_constants_non_overlapping()
    ensures push_constant_ranges_non_overlapping(Seq::empty()),
{
}

/// A layout with no set layouts is compatible with any other
/// at no set indices (vacuously).
pub proof fn lemma_empty_set_layouts_compat(
    layout_a: PipelineLayoutState,
    layout_b: PipelineLayoutState,
    set_index: nat,
)
    requires layout_a.set_layouts.len() == 0,
    ensures !layouts_compatible_at_set(layout_a, layout_b, set_index),
{
}

/// Empty push constant ranges have zero total size.
pub proof fn lemma_empty_push_constants_zero_size()
    ensures total_push_constant_size(Seq::empty()) == 0,
{
}

/// A descriptor set compatible with layout_a is also compatible with
/// layout_b if the layouts are compatible at that set index.
pub proof fn lemma_set_compat_transfers(
    set: DescriptorSetState,
    layout_a: PipelineLayoutState,
    layout_b: PipelineLayoutState,
    set_index: nat,
)
    requires
        descriptor_set_compatible_with_layout(set, layout_a, set_index),
        layouts_compatible_at_set(layout_a, layout_b, set_index),
    ensures
        descriptor_set_compatible_with_layout(set, layout_b, set_index),
{
}

} // verus!
