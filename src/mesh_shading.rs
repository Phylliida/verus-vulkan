use vstd::prelude::*;
use crate::flags::*;
use crate::resource::*;

verus! {

//  ── Types ───────────────────────────────────────────────────────────────

///  Ghost state for a mesh shading pipeline (VK_EXT_mesh_shader).
///
///  Mesh shading replaces the traditional vertex/geometry pipeline with
///  task → mesh shader stages. The mesh shader is mandatory; the task
///  shader is optional.
pub struct MeshPipelineState {
    pub id: nat,
    pub task_shader: Option<nat>,
    pub mesh_shader: nat,
    pub descriptor_set_layouts: Seq<nat>,
    pub max_output_vertices: nat,
    pub max_output_primitives: nat,
    pub alive: bool,
}

///  Parameters for a mesh shader dispatch.
pub struct MeshDispatchParams {
    pub group_count_x: nat,
    pub group_count_y: nat,
    pub group_count_z: nat,
}

///  Record of a mesh dispatch command.
pub struct MeshDispatchRecord {
    pub pipeline_id: nat,
    pub params: MeshDispatchParams,
    pub referenced_resources: Set<ResourceId>,
}

///  Device limits for mesh shading.
pub struct MeshLimits {
    pub max_task_work_group_invocations: nat,
    pub max_mesh_work_group_invocations: nat,
    pub max_mesh_output_vertices: nat,
    pub max_mesh_output_primitives: nat,
    pub max_task_payload_size: nat,
    pub max_draw_mesh_tasks_count: nat,
}

//  ── Spec Functions ──────────────────────────────────────────────────────

///  A mesh pipeline is well-formed: alive, mesh shader present, outputs within limits.
pub open spec fn mesh_pipeline_well_formed(
    state: MeshPipelineState,
    limits: MeshLimits,
) -> bool {
    state.alive
    && state.max_output_vertices <= limits.max_mesh_output_vertices
    && state.max_output_primitives <= limits.max_mesh_output_primitives
}

///  A mesh dispatch is valid: counts > 0 and product within max.
pub open spec fn mesh_dispatch_valid(
    state: MeshPipelineState,
    params: MeshDispatchParams,
    limits: MeshLimits,
) -> bool {
    state.alive
    && params.group_count_x > 0
    && params.group_count_y > 0
    && params.group_count_z > 0
    && params.group_count_x * params.group_count_y * params.group_count_z
        <= limits.max_draw_mesh_tasks_count
}

///  Total workgroups dispatched.
pub open spec fn mesh_dispatch_size(params: MeshDispatchParams) -> nat {
    params.group_count_x * params.group_count_y * params.group_count_z
}

///  Ghost: create a mesh pipeline.
pub open spec fn create_mesh_pipeline_ghost(
    id: nat,
    task_shader: Option<nat>,
    mesh_shader: nat,
    layouts: Seq<nat>,
    max_verts: nat,
    max_prims: nat,
) -> MeshPipelineState {
    MeshPipelineState {
        id,
        task_shader,
        mesh_shader,
        descriptor_set_layouts: layouts,
        max_output_vertices: max_verts,
        max_output_primitives: max_prims,
        alive: true,
    }
}

///  Ghost: destroy a mesh pipeline.
pub open spec fn destroy_mesh_pipeline_ghost(
    state: MeshPipelineState,
) -> MeshPipelineState {
    MeshPipelineState { alive: false, ..state }
}

///  Ghost: record a mesh dispatch command.
pub open spec fn draw_mesh_tasks_ghost(
    state: MeshPipelineState,
    params: MeshDispatchParams,
    resources: Set<ResourceId>,
) -> MeshDispatchRecord {
    MeshDispatchRecord {
        pipeline_id: state.id,
        params,
        referenced_resources: resources,
    }
}

///  Indirect mesh dispatch is valid: buffer bounds + alignment.
pub open spec fn mesh_indirect_valid(
    state: MeshPipelineState,
    buffer_size: nat,
    offset: nat,
    draw_count: nat,
    stride: nat,
    limits: MeshLimits,
) -> bool {
    state.alive
    && stride >= 12  //  3 × u32
    && draw_count <= limits.max_draw_mesh_tasks_count
    && offset + draw_count * stride <= buffer_size
    && offset % 4 == 0
}

///  Pipeline stages used by a mesh pipeline.
pub open spec fn mesh_pipeline_stages(
    state: MeshPipelineState,
) -> PipelineStageFlags {
    if state.task_shader.is_some() {
        PipelineStageFlags {
            stages: set! { STAGE_TASK_SHADER(), STAGE_MESH_SHADER() },
        }
    } else {
        PipelineStageFlags {
            stages: set! { STAGE_MESH_SHADER() },
        }
    }
}

///  Mesh pipelines are incompatible with vertex pipeline stages.
pub open spec fn mesh_excludes_vertex_stages(
    mesh_stages: PipelineStageFlags,
) -> bool {
    !mesh_stages.stages.contains(STAGE_VERTEX_SHADER())
    && !mesh_stages.stages.contains(STAGE_GEOMETRY_SHADER())
    && !mesh_stages.stages.contains(STAGE_TESSELLATION_CONTROL_SHADER())
    && !mesh_stages.stages.contains(STAGE_TESSELLATION_EVALUATION_SHADER())
}

//  ── Proofs ──────────────────────────────────────────────────────────────

///  Well-formed mesh pipeline has a mesh shader (alive).
pub proof fn lemma_mesh_pipeline_has_mesh_shader(
    state: MeshPipelineState,
    limits: MeshLimits,
)
    requires mesh_pipeline_well_formed(state, limits),
    ensures state.alive,
{
}

///  Valid dispatch has positive total size.
pub proof fn lemma_mesh_dispatch_positive_size(
    state: MeshPipelineState,
    params: MeshDispatchParams,
    limits: MeshLimits,
)
    requires mesh_dispatch_valid(state, params, limits),
    ensures mesh_dispatch_size(params) > 0,
{
    vstd::arithmetic::mul::lemma_mul_strictly_positive(
        params.group_count_x as int,
        params.group_count_y as int,
    );
    vstd::arithmetic::mul::lemma_mul_strictly_positive(
        (params.group_count_x * params.group_count_y) as int,
        params.group_count_z as int,
    );
}

///  Created pipeline is alive.
pub proof fn lemma_create_is_alive(
    id: nat,
    task_shader: Option<nat>,
    mesh_shader: nat,
    layouts: Seq<nat>,
    max_verts: nat,
    max_prims: nat,
)
    ensures create_mesh_pipeline_ghost(id, task_shader, mesh_shader, layouts, max_verts, max_prims).alive,
{
}

///  Destroyed pipeline is not alive.
pub proof fn lemma_destroy_not_alive(state: MeshPipelineState)
    ensures !destroy_mesh_pipeline_ghost(state).alive,
{
}

///  Pipeline is valid with or without task shader.
pub proof fn lemma_task_optional(
    id: nat,
    mesh_shader: nat,
    layouts: Seq<nat>,
    limits: MeshLimits,
)
    requires
        limits.max_mesh_output_vertices > 0,
        limits.max_mesh_output_primitives > 0,
    ensures
        mesh_pipeline_well_formed(
            create_mesh_pipeline_ghost(id, None, mesh_shader, layouts, 1, 1),
            limits,
        ),
        mesh_pipeline_well_formed(
            create_mesh_pipeline_ghost(id, Some(0), mesh_shader, layouts, 1, 1),
            limits,
        ),
{
}

///  Valid dispatch respects all limits.
pub proof fn lemma_dispatch_within_limits(
    state: MeshPipelineState,
    params: MeshDispatchParams,
    limits: MeshLimits,
)
    requires mesh_dispatch_valid(state, params, limits),
    ensures
        mesh_dispatch_size(params) <= limits.max_draw_mesh_tasks_count,
{
}

///  Pipeline stages are always non-empty.
pub proof fn lemma_mesh_stages_nonempty(state: MeshPipelineState)
    ensures mesh_pipeline_stages(state).stages.len() > 0,
{
    if state.task_shader.is_some() {
        assert(mesh_pipeline_stages(state).stages.contains(STAGE_TASK_SHADER()));
    } else {
        assert(mesh_pipeline_stages(state).stages.contains(STAGE_MESH_SHADER()));
    }
}

///  Indirect dispatch requires an alive pipeline.
pub proof fn lemma_indirect_requires_well_formed(
    state: MeshPipelineState,
    buffer_size: nat,
    offset: nat,
    count: nat,
    stride: nat,
    limits: MeshLimits,
)
    requires mesh_indirect_valid(state, buffer_size, offset, count, stride, limits),
    ensures state.alive,
{
}

///  Destroy preserves pipeline id.
pub proof fn lemma_destroy_preserves_id(state: MeshPipelineState)
    ensures destroy_mesh_pipeline_ghost(state).id == state.id,
{
}

///  Mesh pipeline stages exclude vertex/geometry/tessellation stages.
pub proof fn lemma_mesh_excludes_vertex(state: MeshPipelineState)
    ensures mesh_excludes_vertex_stages(mesh_pipeline_stages(state)),
{
}

} //  verus!
