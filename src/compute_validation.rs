use vstd::prelude::*;
use crate::recording::*;
use crate::pipeline::*;
use crate::descriptor::*;

verus! {

//  ── Types ───────────────────────────────────────────────────────────────

///  Device limits for compute dispatch.
pub struct ComputeLimits {
    ///  Maximum work group count in each dimension.
    pub max_group_count_x: nat,
    pub max_group_count_y: nat,
    pub max_group_count_z: nat,
}

//  ── Spec Functions ──────────────────────────────────────────────────────

///  Dispatch dimensions are within device limits.
pub open spec fn dispatch_dimensions_valid(
    x: nat,
    y: nat,
    z: nat,
    limits: ComputeLimits,
) -> bool {
    x <= limits.max_group_count_x
    && y <= limits.max_group_count_y
    && z <= limits.max_group_count_z
}

///  Descriptor sets are valid for a compute pipeline.
pub open spec fn compute_descriptors_valid(
    state: RecordingState,
    pipeline: ComputePipelineState,
    descriptor_sets: Map<nat, DescriptorSetState>,
    set_layouts: Map<nat, DescriptorSetLayoutState>,
) -> bool {
    forall|i: int| #![trigger pipeline.descriptor_set_layouts[i]]
        0 <= i < pipeline.descriptor_set_layouts.len() ==> {
        let layout_id = pipeline.descriptor_set_layouts[i];
        let set_index = i as nat;
        state.bound_descriptor_sets.contains_key(set_index)
        && descriptor_sets.contains_key(state.bound_descriptor_sets[set_index])
        && set_layouts.contains_key(layout_id)
        && descriptor_sets[state.bound_descriptor_sets[set_index]].layout_id == layout_id
    }
}

///  Full compute dispatch validation: pipeline + dimensions + descriptors.
pub open spec fn full_dispatch_valid(
    state: RecordingState,
    pipeline: ComputePipelineState,
    limits: ComputeLimits,
    x: nat,
    y: nat,
    z: nat,
    descriptor_sets: Map<nat, DescriptorSetState>,
    set_layouts: Map<nat, DescriptorSetLayoutState>,
) -> bool {
    dispatch_call_valid(state, pipeline)
    && dispatch_dimensions_valid(x, y, z, limits)
    && compute_descriptors_valid(state, pipeline, descriptor_sets, set_layouts)
}

///  A dispatch with zero groups in any dimension does nothing.
pub open spec fn dispatch_is_noop(x: nat, y: nat, z: nat) -> bool {
    x == 0 || y == 0 || z == 0
}

///  A pipeline with no descriptor set layouts needs no descriptor validation.
pub open spec fn compute_pipeline_needs_no_descriptors(
    pipeline: ComputePipelineState,
) -> bool {
    pipeline.descriptor_set_layouts.len() == 0
}

//  ── Proofs ──────────────────────────────────────────────────────────────

///  A zero-dimension dispatch is always within limits.
pub proof fn lemma_zero_dispatch_valid(limits: ComputeLimits)
    ensures
        dispatch_dimensions_valid(0, 0, 0, limits),
{
}

///  If all dimensions are within limits, dispatch is valid.
pub proof fn lemma_within_limits_valid(
    x: nat, y: nat, z: nat,
    limits: ComputeLimits,
)
    requires
        x <= limits.max_group_count_x,
        y <= limits.max_group_count_y,
        z <= limits.max_group_count_z,
    ensures
        dispatch_dimensions_valid(x, y, z, limits),
{
}

///  A compute pipeline with no descriptor layouts trivially satisfies
///  descriptor validation.
pub proof fn lemma_no_layouts_descriptors_valid(
    state: RecordingState,
    pipeline: ComputePipelineState,
    descriptor_sets: Map<nat, DescriptorSetState>,
    set_layouts: Map<nat, DescriptorSetLayoutState>,
)
    requires
        compute_pipeline_needs_no_descriptors(pipeline),
    ensures
        compute_descriptors_valid(state, pipeline, descriptor_sets, set_layouts),
{
}

///  full_dispatch_valid implies dispatch_call_valid.
pub proof fn lemma_full_dispatch_implies_basic(
    state: RecordingState,
    pipeline: ComputePipelineState,
    limits: ComputeLimits,
    x: nat, y: nat, z: nat,
    descriptor_sets: Map<nat, DescriptorSetState>,
    set_layouts: Map<nat, DescriptorSetLayoutState>,
)
    requires
        full_dispatch_valid(state, pipeline, limits, x, y, z, descriptor_sets, set_layouts),
    ensures
        dispatch_call_valid(state, pipeline),
{
}

///  full_dispatch_valid implies dimensions are within limits.
pub proof fn lemma_full_dispatch_implies_dimensions(
    state: RecordingState,
    pipeline: ComputePipelineState,
    limits: ComputeLimits,
    x: nat, y: nat, z: nat,
    descriptor_sets: Map<nat, DescriptorSetState>,
    set_layouts: Map<nat, DescriptorSetLayoutState>,
)
    requires
        full_dispatch_valid(state, pipeline, limits, x, y, z, descriptor_sets, set_layouts),
    ensures
        dispatch_dimensions_valid(x, y, z, limits),
{
}

} //  verus!
