use vstd::prelude::*;

verus! {

//  ── Types ───────────────────────────────────────────────────────────────

///  Shader stages (VK_EXT_shader_object).
pub enum ShaderStage {
    Vertex,
    Fragment,
    Compute,
    Geometry,
    TessControl,
    TessEval,
    Mesh,
    Task,
}

///  State of a shader object.
pub struct ShaderObjectState {
    pub id: nat,
    pub stage: ShaderStage,
    pub alive: bool,
    pub descriptor_set_layouts: Seq<nat>,
    pub push_constant_ranges: Seq<nat>,
}

///  Tracks which shader objects are bound per stage.
pub struct BoundShaderObjects {
    pub vertex: Option<nat>,
    pub fragment: Option<nat>,
    pub compute: Option<nat>,
    pub geometry: Option<nat>,
    pub tess_control: Option<nat>,
    pub tess_eval: Option<nat>,
    pub mesh: Option<nat>,
    pub task: Option<nat>,
}

//  ── Spec Functions ──────────────────────────────────────────────────────

///  Create a fresh shader object.
pub open spec fn create_shader_object(
    id: nat,
    stage: ShaderStage,
    layouts: Seq<nat>,
    push_ranges: Seq<nat>,
) -> ShaderObjectState {
    ShaderObjectState {
        id,
        stage,
        alive: true,
        descriptor_set_layouts: layouts,
        push_constant_ranges: push_ranges,
    }
}

///  Ghost update: destroy a shader object.
pub open spec fn destroy_shader_object(state: ShaderObjectState) -> ShaderObjectState {
    ShaderObjectState {
        alive: false,
        ..state
    }
}

///  A shader object is well-formed.
pub open spec fn shader_object_well_formed(state: ShaderObjectState) -> bool {
    state.alive
}

///  Ghost update: bind a shader object to its stage.
pub open spec fn bind_shader_object(
    bound: BoundShaderObjects,
    shader: ShaderObjectState,
) -> BoundShaderObjects {
    match shader.stage {
        ShaderStage::Vertex => BoundShaderObjects { vertex: Some(shader.id), ..bound },
        ShaderStage::Fragment => BoundShaderObjects { fragment: Some(shader.id), ..bound },
        ShaderStage::Compute => BoundShaderObjects { compute: Some(shader.id), ..bound },
        ShaderStage::Geometry => BoundShaderObjects { geometry: Some(shader.id), ..bound },
        ShaderStage::TessControl => BoundShaderObjects { tess_control: Some(shader.id), ..bound },
        ShaderStage::TessEval => BoundShaderObjects { tess_eval: Some(shader.id), ..bound },
        ShaderStage::Mesh => BoundShaderObjects { mesh: Some(shader.id), ..bound },
        ShaderStage::Task => BoundShaderObjects { task: Some(shader.id), ..bound },
    }
}

///  No shader objects are bound.
pub open spec fn no_shader_objects_bound() -> BoundShaderObjects {
    BoundShaderObjects {
        vertex: None,
        fragment: None,
        compute: None,
        geometry: None,
        tess_control: None,
        tess_eval: None,
        mesh: None,
        task: None,
    }
}

///  Draw calls require at least VS+FS bound when using shader objects.
pub open spec fn shader_objects_draw_valid(bound: BoundShaderObjects) -> bool {
    bound.vertex.is_some()
    && bound.fragment.is_some()
}

///  Dispatch calls require compute shader bound when using shader objects.
pub open spec fn shader_objects_dispatch_valid(bound: BoundShaderObjects) -> bool {
    bound.compute.is_some()
}

///  Get the bound shader id for a given stage.
pub open spec fn get_bound_shader(
    bound: BoundShaderObjects,
    stage: ShaderStage,
) -> Option<nat> {
    match stage {
        ShaderStage::Vertex => bound.vertex,
        ShaderStage::Fragment => bound.fragment,
        ShaderStage::Compute => bound.compute,
        ShaderStage::Geometry => bound.geometry,
        ShaderStage::TessControl => bound.tess_control,
        ShaderStage::TessEval => bound.tess_eval,
        ShaderStage::Mesh => bound.mesh,
        ShaderStage::Task => bound.task,
    }
}

//  ── Lemmas ──────────────────────────────────────────────────────────────

///  A freshly created shader object is alive.
pub proof fn lemma_create_is_alive(
    id: nat, stage: ShaderStage, layouts: Seq<nat>, push_ranges: Seq<nat>,
)
    ensures create_shader_object(id, stage, layouts, push_ranges).alive,
{
}

///  A destroyed shader object is not alive.
pub proof fn lemma_destroy_not_alive(state: ShaderObjectState)
    ensures !destroy_shader_object(state).alive,
{
}

///  Draw valid implies vertex is bound.
pub proof fn lemma_draw_valid_has_vertex(bound: BoundShaderObjects)
    requires shader_objects_draw_valid(bound),
    ensures bound.vertex.is_some(),
{
}

///  Draw valid implies fragment is bound.
pub proof fn lemma_draw_valid_has_fragment(bound: BoundShaderObjects)
    requires shader_objects_draw_valid(bound),
    ensures bound.fragment.is_some(),
{
}

///  Dispatch valid implies compute is bound.
pub proof fn lemma_dispatch_valid_has_compute(bound: BoundShaderObjects)
    requires shader_objects_dispatch_valid(bound),
    ensures bound.compute.is_some(),
{
}

///  Destroying preserves the shader id.
pub proof fn lemma_destroy_preserves_id(state: ShaderObjectState)
    ensures destroy_shader_object(state).id == state.id,
{
}

} //  verus!
