use vstd::prelude::*;
use crate::ray_tracing_pipeline::*;
use crate::acceleration_structure::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// A strided device address region for SBT entries.
pub struct StridedDeviceAddressRegion {
    pub device_address: nat,
    pub stride: nat,
    pub size: nat,
}

/// Parameters for an indirect trace rays dispatch.
pub struct IndirectTraceRaysParams {
    pub indirect_buffer_id: nat,
    pub indirect_offset: nat,
}

/// State for VK_KHR_ray_tracing_maintenance1 features.
pub struct TraceRaysMaintenance1State {
    pub pipeline_id: nat,
    pub inline_enabled: bool,
    pub max_ray_hit_attribute_size: nat,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// A strided device address region is well-formed.
pub open spec fn strided_region_well_formed(region: StridedDeviceAddressRegion) -> bool {
    region.stride > 0
    && region.size > 0
    && region.size % region.stride == 0
}

/// A strided region is aligned to the given alignment.
pub open spec fn strided_region_aligned(
    region: StridedDeviceAddressRegion,
    alignment: nat,
) -> bool {
    alignment > 0
    && region.device_address % alignment == 0
    && region.stride % alignment == 0
}

/// Indirect trace rays dispatch is valid.
pub open spec fn indirect_trace_rays_valid(
    pipeline: RayTracingPipelineState,
    tlas: AccelerationStructureState,
    buffer_size: nat,
    params: IndirectTraceRaysParams,
) -> bool {
    pipeline.alive
    && rt_pipeline_well_formed(pipeline)
    && tlas_well_formed(tlas)
    && tlas.built
    && params.indirect_offset + 16 <= buffer_size
    && params.indirect_offset % 4 == 0
}

/// Trace rays with explicit SBT regions is valid.
pub open spec fn trace_rays_with_regions_valid(
    pipeline: RayTracingPipelineState,
    tlas: AccelerationStructureState,
    raygen: StridedDeviceAddressRegion,
    miss: StridedDeviceAddressRegion,
    hit: StridedDeviceAddressRegion,
    callable: StridedDeviceAddressRegion,
    params: TraceRaysParams,
) -> bool {
    rt_pipeline_well_formed(pipeline)
    && tlas_well_formed(tlas)
    && tlas.built
    && strided_region_well_formed(raygen)
    && strided_region_well_formed(miss)
    && strided_region_well_formed(hit)
    && strided_region_well_formed(callable)
    && raygen.stride == raygen.size  // raygen is a single entry
    && params.width > 0
    && params.height > 0
    && params.depth > 0
}

/// Whether inline ray tracing is enabled.
pub open spec fn inline_ray_tracing_enabled(state: TraceRaysMaintenance1State) -> bool {
    state.inline_enabled
}

/// Create a maintenance1 state.
pub open spec fn create_maintenance1_state(
    pipeline_id: nat,
    inline: bool,
    max_attr: nat,
) -> TraceRaysMaintenance1State {
    TraceRaysMaintenance1State {
        pipeline_id: pipeline_id,
        inline_enabled: inline,
        max_ray_hit_attribute_size: max_attr,
    }
}

/// Ray hit attribute size is within limits.
pub open spec fn maintenance1_ray_hit_attribute_valid(
    state: TraceRaysMaintenance1State,
    attribute_size: nat,
) -> bool {
    attribute_size <= state.max_ray_hit_attribute_size
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// A well-formed strided region has at least one entry.
pub proof fn lemma_strided_region_has_entries(region: StridedDeviceAddressRegion)
    requires strided_region_well_formed(region),
    ensures region.size / region.stride >= 1,
{
    // size > 0, stride > 0, size % stride == 0 → size >= stride → size/stride >= 1
    assert(region.size >= region.stride) by(nonlinear_arith)
        requires
            region.size > 0nat,
            region.stride > 0nat,
            region.size % region.stride == 0nat,
    ;
    assert(region.size / region.stride >= 1) by(nonlinear_arith)
        requires
            region.size >= region.stride,
            region.stride > 0nat,
    ;
}

/// Indirect valid implies pipeline is alive.
pub proof fn lemma_indirect_requires_pipeline_alive(
    pipeline: RayTracingPipelineState,
    tlas: AccelerationStructureState,
    buffer_size: nat,
    params: IndirectTraceRaysParams,
)
    requires indirect_trace_rays_valid(pipeline, tlas, buffer_size, params),
    ensures pipeline.alive,
{
}

/// Indirect valid implies TLAS is built.
pub proof fn lemma_indirect_requires_built_tlas(
    pipeline: RayTracingPipelineState,
    tlas: AccelerationStructureState,
    buffer_size: nat,
    params: IndirectTraceRaysParams,
)
    requires indirect_trace_rays_valid(pipeline, tlas, buffer_size, params),
    ensures tlas.built,
{
}

/// Raygen region with stride == size and well-formed has exactly one entry.
pub proof fn lemma_raygen_is_single_entry(region: StridedDeviceAddressRegion)
    requires
        strided_region_well_formed(region),
        region.stride == region.size,
    ensures region.size / region.stride == 1,
{
}

/// Regions valid implies pipeline is well-formed.
pub proof fn lemma_regions_valid_implies_pipeline_valid(
    pipeline: RayTracingPipelineState,
    tlas: AccelerationStructureState,
    raygen: StridedDeviceAddressRegion,
    miss: StridedDeviceAddressRegion,
    hit: StridedDeviceAddressRegion,
    callable: StridedDeviceAddressRegion,
    params: TraceRaysParams,
)
    requires trace_rays_with_regions_valid(pipeline, tlas, raygen, miss, hit, callable, params),
    ensures rt_pipeline_well_formed(pipeline),
{
}

/// Creating with inline=true enables inline ray tracing.
pub proof fn lemma_inline_create(pipeline_id: nat, max_attr: nat)
    ensures inline_ray_tracing_enabled(create_maintenance1_state(pipeline_id, true, max_attr)),
{
}

/// Valid attribute size is bounded by max.
pub proof fn lemma_attribute_size_bounded(
    state: TraceRaysMaintenance1State,
    attribute_size: nat,
)
    requires maintenance1_ray_hit_attribute_valid(state, attribute_size),
    ensures attribute_size <= state.max_ray_hit_attribute_size,
{
}

/// Indirect valid implies offset is 4-byte aligned.
pub proof fn lemma_indirect_offset_aligned(
    pipeline: RayTracingPipelineState,
    tlas: AccelerationStructureState,
    buffer_size: nat,
    params: IndirectTraceRaysParams,
)
    requires indirect_trace_rays_valid(pipeline, tlas, buffer_size, params),
    ensures params.indirect_offset % 4 == 0,
{
}

} // verus!
