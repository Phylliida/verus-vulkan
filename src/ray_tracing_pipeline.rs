use vstd::prelude::*;
use crate::acceleration_structure::*;

verus! {

// ── Types ──────────────────────────────────────────────────────────────

/// A ray generation shader entry.
pub struct RayGenShader {
    pub id: nat,
}

/// A miss shader entry.
pub struct MissShader {
    pub id: nat,
}

/// A hit group combining closest-hit, any-hit, and intersection shaders.
pub struct HitGroup {
    pub closest_hit: Option<nat>,
    pub any_hit: Option<nat>,
    pub intersection: Option<nat>,
}

/// Shader binding table: maps shader indices to shader groups.
pub struct ShaderBindingTable {
    /// Ray generation shaders.
    pub ray_gen: Seq<RayGenShader>,
    /// Miss shaders.
    pub miss: Seq<MissShader>,
    /// Hit groups.
    pub hit: Seq<HitGroup>,
    /// Callable shader IDs.
    pub callable: Seq<nat>,
    /// Buffer holding the SBT data.
    pub buffer_id: nat,
}

/// Ghost state for a ray tracing pipeline.
pub struct RayTracingPipelineState {
    /// Unique pipeline identifier.
    pub id: nat,
    /// Maximum ray recursion depth.
    pub max_recursion_depth: nat,
    /// Shader group identifiers.
    pub shader_groups: Seq<nat>,
    /// Shader binding table.
    pub sbt: ShaderBindingTable,
    /// False after destruction.
    pub alive: bool,
}

/// Parameters for a vkCmdTraceRaysKHR dispatch.
pub struct TraceRaysParams {
    pub width: nat,
    pub height: nat,
    pub depth: nat,
}

/// Result of a trace rays dispatch (ghost state update).
pub struct TraceRaysRecord {
    pub pipeline_id: nat,
    pub tlas_id: nat,
    pub params: TraceRaysParams,
    pub generation: nat,
}

// ── Spec Functions ──────────────────────────────────────────────────

/// The shader binding table is well-formed.
pub open spec fn sbt_well_formed(sbt: ShaderBindingTable) -> bool {
    // Must have at least one ray gen shader
    sbt.ray_gen.len() > 0
}

/// The SBT covers the pipeline's shader groups.
pub open spec fn sbt_covers_pipeline(
    sbt: ShaderBindingTable,
    pipeline: RayTracingPipelineState,
) -> bool {
    sbt.ray_gen.len() + sbt.miss.len() + sbt.hit.len() + sbt.callable.len()
        >= pipeline.shader_groups.len()
}

/// A ray tracing pipeline is well-formed.
pub open spec fn rt_pipeline_well_formed(
    pipeline: RayTracingPipelineState,
) -> bool {
    pipeline.alive
    && pipeline.max_recursion_depth > 0
    && pipeline.shader_groups.len() > 0
    && sbt_well_formed(pipeline.sbt)
}

/// All preconditions for vkCmdTraceRaysKHR.
pub open spec fn trace_rays_valid(
    pipeline: RayTracingPipelineState,
    tlas: AccelerationStructureState,
    params: TraceRaysParams,
) -> bool {
    rt_pipeline_well_formed(pipeline)
    && tlas_well_formed(tlas)
    && tlas.built
    && params.width > 0
    && params.height > 0
    && params.depth > 0
    && sbt_covers_pipeline(pipeline.sbt, pipeline)
}

/// Ghost update: record a trace rays dispatch.
pub open spec fn trace_rays_ghost(
    pipeline: RayTracingPipelineState,
    tlas: AccelerationStructureState,
    params: TraceRaysParams,
    generation: nat,
) -> TraceRaysRecord {
    TraceRaysRecord {
        pipeline_id: pipeline.id,
        tlas_id: tlas.id,
        params: params,
        generation: generation,
    }
}

/// Hit group has at least one shader.
pub open spec fn hit_group_non_empty(hg: HitGroup) -> bool {
    matches!(hg.closest_hit, Some(_)) || matches!(hg.any_hit, Some(_)) || matches!(hg.intersection, Some(_))
}

/// All hit groups in the SBT are non-empty.
pub open spec fn all_hit_groups_non_empty(sbt: ShaderBindingTable) -> bool {
    forall|i: nat|
        #![trigger sbt.hit[i as int]]
        i < sbt.hit.len()
        ==> hit_group_non_empty(sbt.hit[i as int])
}

/// Total dispatch size (product of dimensions).
pub open spec fn trace_rays_dispatch_size(params: TraceRaysParams) -> nat {
    params.width * params.height * params.depth
}

/// Max recursion depth is within device limits.
pub open spec fn recursion_within_limits(
    pipeline: RayTracingPipelineState,
    device_max: nat,
) -> bool {
    pipeline.max_recursion_depth <= device_max
}

/// The SBT buffer must be alive.
pub open spec fn sbt_buffer_live(
    sbt: ShaderBindingTable,
    live_buffers: Set<nat>,
) -> bool {
    live_buffers.contains(sbt.buffer_id)
}

/// Pipeline and TLAS have distinct IDs (sanity check).
pub open spec fn pipeline_tlas_distinct(
    pipeline: RayTracingPipelineState,
    tlas: AccelerationStructureState,
) -> bool {
    pipeline.id != tlas.id
}

/// All ray gen shaders have distinct IDs.
pub open spec fn ray_gen_ids_distinct(sbt: ShaderBindingTable) -> bool {
    forall|i: nat, j: nat|
        #![trigger sbt.ray_gen[i as int], sbt.ray_gen[j as int]]
        i < sbt.ray_gen.len() && j < sbt.ray_gen.len() && i != j
        ==> sbt.ray_gen[i as int].id != sbt.ray_gen[j as int].id
}

/// All miss shaders have distinct IDs.
pub open spec fn miss_ids_distinct(sbt: ShaderBindingTable) -> bool {
    forall|i: nat, j: nat|
        #![trigger sbt.miss[i as int], sbt.miss[j as int]]
        i < sbt.miss.len() && j < sbt.miss.len() && i != j
        ==> sbt.miss[i as int].id != sbt.miss[j as int].id
}

// ── Proofs ──────────────────────────────────────────────────────────

/// Trace rays requires a built TLAS.
pub proof fn lemma_trace_rays_requires_built_tlas(
    pipeline: RayTracingPipelineState,
    tlas: AccelerationStructureState,
    params: TraceRaysParams,
)
    requires trace_rays_valid(pipeline, tlas, params),
    ensures tlas.built && tlas.alive,
{
}

/// SBT buffer must be live for trace rays.
pub proof fn lemma_sbt_buffer_must_be_live(
    pipeline: RayTracingPipelineState,
    live_buffers: Set<nat>,
)
    requires
        rt_pipeline_well_formed(pipeline),
        sbt_buffer_live(pipeline.sbt, live_buffers),
    ensures live_buffers.contains(pipeline.sbt.buffer_id),
{
}

/// Max recursion depth is bounded.
pub proof fn lemma_max_recursion_bounded(
    pipeline: RayTracingPipelineState,
    device_max: nat,
)
    requires
        rt_pipeline_well_formed(pipeline),
        recursion_within_limits(pipeline, device_max),
    ensures pipeline.max_recursion_depth <= device_max,
{
}

/// Trace rays dispatch is non-zero in all dimensions.
pub proof fn lemma_trace_rays_nonzero_dispatch(
    pipeline: RayTracingPipelineState,
    tlas: AccelerationStructureState,
    params: TraceRaysParams,
)
    requires trace_rays_valid(pipeline, tlas, params),
    ensures
        params.width > 0,
        params.height > 0,
        params.depth > 0,
{
}

/// Trace rays ghost record captures correct pipeline and tlas IDs.
pub proof fn lemma_trace_rays_ghost_ids(
    pipeline: RayTracingPipelineState,
    tlas: AccelerationStructureState,
    params: TraceRaysParams,
    gen: nat,
)
    ensures
        trace_rays_ghost(pipeline, tlas, params, gen).pipeline_id == pipeline.id,
        trace_rays_ghost(pipeline, tlas, params, gen).tlas_id == tlas.id,
{
}

/// A well-formed pipeline has at least one shader group.
pub proof fn lemma_pipeline_has_shaders(
    pipeline: RayTracingPipelineState,
)
    requires rt_pipeline_well_formed(pipeline),
    ensures pipeline.shader_groups.len() > 0,
{
}

/// A well-formed pipeline has a well-formed SBT.
pub proof fn lemma_pipeline_has_valid_sbt(
    pipeline: RayTracingPipelineState,
)
    requires rt_pipeline_well_formed(pipeline),
    ensures sbt_well_formed(pipeline.sbt),
{
}

/// An SBT with one ray gen shader and zero others is well-formed.
pub proof fn lemma_minimal_sbt_well_formed(rg: RayGenShader)
    ensures sbt_well_formed(ShaderBindingTable {
        ray_gen: seq![rg],
        miss: Seq::empty(),
        hit: Seq::empty(),
        callable: Seq::empty(),
        buffer_id: 0,
    }),
{
}

/// Building a BLAS then checking validity: built flag is set.
pub proof fn lemma_build_then_trace_ready(
    blas: AccelerationStructureState,
    tlas: AccelerationStructureState,
    blas_map: Map<nat, AccelerationStructureState>,
)
    requires
        blas_well_formed(blas),
        !blas.built,
    ensures
        build_as_ghost(blas, ASBuildMode::Build).built,
{
}

/// Dispatch size is positive when all dimensions are positive.
pub proof fn lemma_dispatch_size_positive(params: TraceRaysParams)
    requires
        params.width > 0,
        params.height > 0,
        params.depth > 0,
    ensures trace_rays_dispatch_size(params) > 0,
{
    assert(params.width * params.height > 0) by(nonlinear_arith)
        requires params.width > 0nat, params.height > 0nat;
    assert(params.width * params.height * params.depth > 0) by(nonlinear_arith)
        requires params.width * params.height > 0nat, params.depth > 0nat;
}

/// Trace rays ghost preserves the params.
pub proof fn lemma_trace_rays_ghost_params(
    pipeline: RayTracingPipelineState,
    tlas: AccelerationStructureState,
    params: TraceRaysParams,
    gen: nat,
)
    ensures trace_rays_ghost(pipeline, tlas, params, gen).params == params,
{
}

/// Empty SBT (no ray gen) is NOT well-formed.
pub proof fn lemma_empty_sbt_not_well_formed()
    ensures !sbt_well_formed(ShaderBindingTable {
        ray_gen: Seq::empty(),
        miss: Seq::empty(),
        hit: Seq::empty(),
        callable: Seq::empty(),
        buffer_id: 0,
    }),
{
}

/// Trace rays validity implies pipeline is alive.
pub proof fn lemma_trace_rays_pipeline_alive(
    pipeline: RayTracingPipelineState,
    tlas: AccelerationStructureState,
    params: TraceRaysParams,
)
    requires trace_rays_valid(pipeline, tlas, params),
    ensures pipeline.alive,
{
}

/// SBT coverage is reflexive when sizes match.
pub proof fn lemma_sbt_covers_when_sizes_match(
    pipeline: RayTracingPipelineState,
)
    requires
        pipeline.sbt.ray_gen.len() + pipeline.sbt.miss.len()
        + pipeline.sbt.hit.len() + pipeline.sbt.callable.len()
        >= pipeline.shader_groups.len(),
    ensures sbt_covers_pipeline(pipeline.sbt, pipeline),
{
}

// ── Extended Specs ──────────────────────────────────────────────────

/// Total shader entries in the SBT.
pub open spec fn sbt_total_entries(sbt: ShaderBindingTable) -> nat {
    sbt.ray_gen.len() + sbt.miss.len() + sbt.hit.len() + sbt.callable.len()
}

/// Number of hit groups in the SBT.
pub open spec fn sbt_hit_group_count(sbt: ShaderBindingTable) -> nat {
    sbt.hit.len()
}

/// Number of miss shaders in the SBT.
pub open spec fn sbt_miss_count(sbt: ShaderBindingTable) -> nat {
    sbt.miss.len()
}

/// Number of ray gen shaders in the SBT.
pub open spec fn sbt_ray_gen_count(sbt: ShaderBindingTable) -> nat {
    sbt.ray_gen.len()
}

/// Total shader groups in the pipeline.
pub open spec fn rt_pipeline_total_shaders(pipeline: RayTracingPipelineState) -> nat {
    pipeline.shader_groups.len()
}

/// Ghost update: destroy a ray tracing pipeline.
pub open spec fn destroy_rt_pipeline_ghost(
    pipeline: RayTracingPipelineState,
) -> RayTracingPipelineState
    recommends pipeline.alive,
{
    RayTracingPipelineState {
        alive: false,
        ..pipeline
    }
}

/// Pipeline uses any-hit shaders (at least one hit group has any_hit).
pub open spec fn rt_pipeline_uses_any_hit(sbt: ShaderBindingTable) -> bool {
    exists|i: nat|
        #![trigger sbt.hit[i as int]]
        i < sbt.hit.len()
        && sbt.hit[i as int].any_hit.is_some()
}

/// Pipeline uses intersection shaders.
pub open spec fn rt_pipeline_uses_intersection(sbt: ShaderBindingTable) -> bool {
    exists|i: nat|
        #![trigger sbt.hit[i as int]]
        i < sbt.hit.len()
        && sbt.hit[i as int].intersection.is_some()
}

/// Trace rays parameters have valid (non-zero) dimensions.
pub open spec fn trace_rays_params_valid(params: TraceRaysParams) -> bool {
    params.width > 0 && params.height > 0 && params.depth > 0
}

/// Trace rays is 2D (depth == 1).
pub open spec fn trace_rays_is_2d(params: TraceRaysParams) -> bool {
    params.depth == 1 && params.width > 0 && params.height > 0
}

/// Two trace ray records target the same pipeline.
pub open spec fn same_pipeline(r1: TraceRaysRecord, r2: TraceRaysRecord) -> bool {
    r1.pipeline_id == r2.pipeline_id
}

/// Two trace ray records target the same TLAS.
pub open spec fn same_tlas(r1: TraceRaysRecord, r2: TraceRaysRecord) -> bool {
    r1.tlas_id == r2.tlas_id
}

/// A destroyed pipeline is not well-formed.
pub open spec fn rt_pipeline_destroyed(pipeline: RayTracingPipelineState) -> bool {
    !pipeline.alive
}

// ── Extended Proofs ────────────────────────────────────────────────

/// Destroying a RT pipeline sets alive to false.
/// Caller must prove the pipeline is alive before destroying.
pub proof fn lemma_destroy_rt_pipeline_not_alive(
    pipeline: RayTracingPipelineState,
)
    requires pipeline.alive,
    ensures !destroy_rt_pipeline_ghost(pipeline).alive,
{
}

/// Destroying a RT pipeline preserves the ID.
pub proof fn lemma_destroy_rt_pipeline_preserves_id(
    pipeline: RayTracingPipelineState,
)
    ensures destroy_rt_pipeline_ghost(pipeline).id == pipeline.id,
{
}

/// Destroying a RT pipeline preserves the SBT.
pub proof fn lemma_destroy_rt_pipeline_preserves_sbt(
    pipeline: RayTracingPipelineState,
)
    ensures destroy_rt_pipeline_ghost(pipeline).sbt == pipeline.sbt,
{
}

/// SBT total entries >= ray gen count.
pub proof fn lemma_sbt_total_entries_geq_ray_gen(sbt: ShaderBindingTable)
    ensures sbt_total_entries(sbt) >= sbt_ray_gen_count(sbt),
{
}

/// A well-formed SBT has positive total entries.
pub proof fn lemma_sbt_well_formed_positive_entries(sbt: ShaderBindingTable)
    requires sbt_well_formed(sbt),
    ensures sbt_total_entries(sbt) > 0,
{
}

/// A well-formed pipeline has positive total shaders.
pub proof fn lemma_pipeline_total_shaders_positive(
    pipeline: RayTracingPipelineState,
)
    requires rt_pipeline_well_formed(pipeline),
    ensures rt_pipeline_total_shaders(pipeline) > 0,
{
}

/// Trace rays ghost captures the generation.
pub proof fn lemma_trace_rays_ghost_generation(
    pipeline: RayTracingPipelineState,
    tlas: AccelerationStructureState,
    params: TraceRaysParams,
    gen: nat,
)
    ensures trace_rays_ghost(pipeline, tlas, params, gen).generation == gen,
{
}

/// A destroyed pipeline is not well-formed.
pub proof fn lemma_dead_pipeline_not_well_formed(
    pipeline: RayTracingPipelineState,
)
    requires !pipeline.alive,
    ensures !rt_pipeline_well_formed(pipeline),
{
}

/// A destroyed pipeline is flagged as destroyed.
pub proof fn lemma_destroyed_pipeline_is_destroyed(
    pipeline: RayTracingPipelineState,
)
    ensures rt_pipeline_destroyed(destroy_rt_pipeline_ghost(pipeline)),
{
}

/// Same pipeline is reflexive.
pub proof fn lemma_same_pipeline_reflexive(r: TraceRaysRecord)
    ensures same_pipeline(r, r),
{
}

/// Same TLAS is reflexive.
pub proof fn lemma_same_tlas_reflexive(r: TraceRaysRecord)
    ensures same_tlas(r, r),
{
}

/// Same pipeline is symmetric.
pub proof fn lemma_same_pipeline_symmetric(r1: TraceRaysRecord, r2: TraceRaysRecord)
    requires same_pipeline(r1, r2),
    ensures same_pipeline(r2, r1),
{
}

/// Same TLAS is symmetric.
pub proof fn lemma_same_tlas_symmetric(r1: TraceRaysRecord, r2: TraceRaysRecord)
    requires same_tlas(r1, r2),
    ensures same_tlas(r2, r1),
{
}

/// Trace rays valid implies params are valid.
pub proof fn lemma_trace_rays_valid_params(
    pipeline: RayTracingPipelineState,
    tlas: AccelerationStructureState,
    params: TraceRaysParams,
)
    requires trace_rays_valid(pipeline, tlas, params),
    ensures trace_rays_params_valid(params),
{
}

/// A 2D trace rays has depth == 1.
pub proof fn lemma_2d_trace_depth_one(params: TraceRaysParams)
    requires trace_rays_is_2d(params),
    ensures params.depth == 1,
{
}

/// 2D trace rays has a positive dispatch size.
pub proof fn lemma_2d_trace_positive_dispatch(params: TraceRaysParams)
    requires trace_rays_is_2d(params),
    ensures trace_rays_dispatch_size(params) == params.width * params.height,
{
    assert(params.width * params.height * 1 == params.width * params.height)
        by(nonlinear_arith)
        requires params.width > 0nat, params.height > 0nat;
}

/// Destroying preserves max recursion depth.
pub proof fn lemma_destroy_preserves_recursion(
    pipeline: RayTracingPipelineState,
)
    ensures
        destroy_rt_pipeline_ghost(pipeline).max_recursion_depth
            == pipeline.max_recursion_depth,
{
}

/// Destroying preserves shader groups.
pub proof fn lemma_destroy_preserves_shader_groups(
    pipeline: RayTracingPipelineState,
)
    ensures
        destroy_rt_pipeline_ghost(pipeline).shader_groups
            == pipeline.shader_groups,
{
}

} // verus!
