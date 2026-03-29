use vstd::prelude::*;
use crate::shader_module::*;

verus! {

///  Runtime wrapper for a VkShaderModule.
pub struct RuntimeShaderModule {
    ///  Opaque handle (maps to VkShaderModule).
    pub handle: u64,
    ///  Ghost model of the shader module state.
    pub state: Ghost<ShaderModuleState>,
}

impl View for RuntimeShaderModule {
    type V = ShaderModuleState;
    open spec fn view(&self) -> ShaderModuleState { self.state@ }
}

///  Well-formedness of the runtime shader module.
pub open spec fn runtime_shader_module_wf(sm: &RuntimeShaderModule) -> bool {
    shader_module_well_formed(sm@)
}

///  Shader module is alive.
pub open spec fn runtime_shader_module_alive(sm: &RuntimeShaderModule) -> bool {
    sm@.alive
}

///  Proof: a well-formed runtime shader module is alive.
pub proof fn lemma_runtime_shader_module_wf_alive(sm: &RuntimeShaderModule)
    requires runtime_shader_module_wf(sm),
    ensures sm@.alive,
{
}

} //  verus!
