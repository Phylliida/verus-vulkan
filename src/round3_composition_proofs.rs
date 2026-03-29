use vstd::prelude::*;
use crate::ray_tracing_pipeline::*;
use crate::ray_tracing_maintenance::*;
use crate::acceleration_structure::*;
use crate::depth_clamp_control::*;
use crate::depth_stencil::*;
use crate::fragment_shading_rate::*;
use crate::variable_rate_shading::*;
use crate::nested_command_buffers::*;

verus! {

//  ══════════════════════════════════════════════════════════════════════
//  Chain 13: Ray Tracing Maintenance + Pipeline Lifecycle
//  ══════════════════════════════════════════════════════════════════════

///  Full lifecycle: create RT pipeline → validate indirect trace → pipeline alive + TLAS built.
pub proof fn lemma_indirect_trace_full_lifecycle(
    pipeline: RayTracingPipelineState,
    tlas: AccelerationStructureState,
    buffer_size: nat,
    params: IndirectTraceRaysParams,
)
    requires
        indirect_trace_rays_valid(pipeline, tlas, buffer_size, params),
    ensures
        pipeline.alive,
        tlas.built,
        rt_pipeline_well_formed(pipeline),
        tlas_well_formed(tlas),
{
    lemma_indirect_requires_pipeline_alive(pipeline, tlas, buffer_size, params);
    lemma_indirect_requires_built_tlas(pipeline, tlas, buffer_size, params);
}

///  Trace rays with regions implies the SBT is well-formed.
pub proof fn lemma_regions_vs_sbt_consistency(
    pipeline: RayTracingPipelineState,
    tlas: AccelerationStructureState,
    raygen: StridedDeviceAddressRegion,
    miss: StridedDeviceAddressRegion,
    hit: StridedDeviceAddressRegion,
    callable: StridedDeviceAddressRegion,
    params: TraceRaysParams,
)
    requires trace_rays_with_regions_valid(pipeline, tlas, raygen, miss, hit, callable, params),
    ensures
        rt_pipeline_well_formed(pipeline),
        sbt_well_formed(pipeline.sbt),
{
    lemma_regions_valid_implies_pipeline_valid(pipeline, tlas, raygen, miss, hit, callable, params);
    lemma_pipeline_has_valid_sbt(pipeline);
}

///  Maintenance1 with inline enabled means pipeline_id is set (non-trivial construction).
pub proof fn lemma_maintenance1_inline_requires_pipeline(
    pipeline_id: nat,
    max_attr: nat,
)
    ensures ({
        let state = create_maintenance1_state(pipeline_id, true, max_attr);
        inline_ray_tracing_enabled(state) && state.pipeline_id == pipeline_id
    }),
{
    lemma_inline_create(pipeline_id, max_attr);
}

//  ══════════════════════════════════════════════════════════════════════
//  Chain 14: Depth Clamp + Depth Stencil Integration
//  ══════════════════════════════════════════════════════════════════════

///  UserDefined clamp + depth test enabled → clamp range is valid.
pub proof fn lemma_depth_clamp_with_depth_test(
    clamp: DepthClampState,
    ds: DepthStencilState,
)
    requires
        depth_clamp_state_well_formed(clamp),
        depth_stencil_well_formed(ds),
        ds.depth_test_enable,
        matches!(clamp.mode, DepthClampMode::UserDefined),
    ensures depth_clamp_range_valid(clamp.range),
{
    lemma_user_defined_requires_valid_range(clamp);
}

///  Disabled clamp doesn't affect depth/stencil output.
pub proof fn lemma_disabled_clamp_preserves_depth_stencil(
    clamp: DepthClampState,
    ds: DepthStencilState,
)
    requires
        depth_clamp_state_well_formed(clamp),
        matches!(clamp.mode, DepthClampMode::Disabled),
    ensures !depth_clamp_affects_output(clamp),
{
    lemma_disabled_no_output_effect(clamp);
}

///  ZeroOne clamp mode is compatible with standard [0,1] depth bounds.
pub proof fn lemma_zero_one_clamp_compatible_with_bounds(
    clamp: DepthClampState,
    depth: int,
)
    requires
        matches!(clamp.mode, DepthClampMode::ZeroOne),
        depth_value_in_clamp_range(clamp, depth),
    ensures 0 <= depth && depth <= 1,
{
    lemma_zero_one_bounds_depth(clamp, depth);
}

//  ══════════════════════════════════════════════════════════════════════
//  Chain 15: Fragment Shading Rate + VRS Composition
//  ══════════════════════════════════════════════════════════════════════

///  Default FSR state with all-Keep combiners gives Rate1x1 (matches VRS default).
pub proof fn lemma_fsr_default_matches_vrs_default()
    ensures fsr_effective_rate(default_shading_rate_state()) == ShadingRate::Rate1x1,
{
    let state = default_shading_rate_state();
    lemma_fsr_effective_rate_with_keep_keep(state);
}

///  Well-formed FSR attachment has positive texel dims (compatible with VRS attachment check).
pub proof fn lemma_fsr_attachment_covers_vrs_framebuffer(
    att: FragmentShadingRateAttachment,
    props: FragmentShadingRateProperties,
)
    requires fsr_attachment_well_formed(att, props),
    ensures
        att.texel_width > 0,
        att.texel_height > 0,
        att.layer_count > 0,
{
    lemma_fsr_attachment_covers(att, props);
}

///  Keep/Keep combiners propagate the pipeline rate through both stages.
pub proof fn lemma_fsr_pipeline_rate_propagates(state: ShadingRateState)
    requires
        matches!(state.combiner_op_0, ShadingRateCombinerOp::Keep),
        matches!(state.combiner_op_1, ShadingRateCombinerOp::Keep),
    ensures fsr_effective_rate(state) == state.pipeline_rate,
{
    lemma_fsr_effective_rate_with_keep_keep(state);
}

//  ══════════════════════════════════════════════════════════════════════
//  Chain 16: Nested CB + Recording State
//  ══════════════════════════════════════════════════════════════════════

///  Nest + unnest roundtrip preserves the nesting level.
pub proof fn lemma_nested_execution_preserves_level(state: NestedCommandBufferState)
    ensures
        nesting_depth(unnest_command_buffer(nest_command_buffer(state)))
            == nesting_depth(state),
{
    lemma_nest_unnest_roundtrip(state);
}

///  Initial nesting state has level 0.
pub proof fn lemma_initial_nesting_at_top_level(limits: NestedCommandBufferLimits)
    ensures nesting_depth(initial_nesting_state(limits)) == 0,
{
    lemma_initial_level_zero(limits);
}

///  After nesting, depth is bounded by limits.max + 1 at most.
pub proof fn lemma_nested_depth_bounded(
    state: NestedCommandBufferState,
    limits: NestedCommandBufferLimits,
)
    requires
        nested_cb_well_formed(state, limits),
        can_nest_deeper(state, limits),
    ensures
        nesting_depth(nest_command_buffer(state))
            <= limits.max_command_buffer_nesting_level,
{
    lemma_can_nest_implies_well_formed_after(state, limits);
}

} //  verus!
