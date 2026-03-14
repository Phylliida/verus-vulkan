use vstd::prelude::*;

verus! {

// ── Types ────────────────────────────────────────────────────────────

/// Shader stage kind — matches VkShaderStageFlagBits for vertex/fragment/compute.
pub enum ShaderStageKind {
    Vertex,
    Fragment,
    Compute,
}

/// Ghost model for a VkShaderModule object.
/// Wraps a compiled SPIR-V module with lifecycle tracking.
pub struct ShaderModuleState {
    /// Unique identifier.
    pub id: nat,
    /// Whether this shader module is alive (not destroyed).
    pub alive: bool,
    /// Which pipeline stage this shader is for.
    pub stage: ShaderStageKind,
}

// ── Spec Functions ───────────────────────────────────────────────────

/// A shader module is well-formed iff it is alive.
pub open spec fn shader_module_well_formed(sm: ShaderModuleState) -> bool {
    sm.alive
}

/// Ghost update: destroy a shader module.
pub open spec fn destroy_shader_module_ghost(sm: ShaderModuleState) -> ShaderModuleState
    recommends sm.alive,
{
    ShaderModuleState { alive: false, ..sm }
}

/// The shader module is a vertex shader.
pub open spec fn shader_module_is_vertex(sm: ShaderModuleState) -> bool {
    sm.stage == ShaderStageKind::Vertex
}

/// The shader module is a fragment shader.
pub open spec fn shader_module_is_fragment(sm: ShaderModuleState) -> bool {
    sm.stage == ShaderStageKind::Fragment
}

// ── Proofs ───────────────────────────────────────────────────────────

/// A freshly created shader module is alive.
pub proof fn lemma_create_shader_module_alive(id: nat, stage: ShaderStageKind)
    ensures shader_module_well_formed(ShaderModuleState { id, alive: true, stage }),
{
}

/// After destroying, a shader module is not alive.
pub proof fn lemma_destroy_shader_module_not_alive(sm: ShaderModuleState)
    requires sm.alive,
    ensures !destroy_shader_module_ghost(sm).alive,
{
}

/// Destroying a shader module preserves its id.
pub proof fn lemma_destroy_shader_module_preserves_id(sm: ShaderModuleState)
    ensures destroy_shader_module_ghost(sm).id == sm.id,
{
}

/// Destroying a shader module preserves its stage.
pub proof fn lemma_destroy_shader_module_preserves_stage(sm: ShaderModuleState)
    ensures destroy_shader_module_ghost(sm).stage == sm.stage,
{
}

} // verus!
