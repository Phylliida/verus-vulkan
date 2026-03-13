use vstd::prelude::*;
use crate::bindless::*;
use crate::descriptor::*;

verus! {

/// Runtime wrapper for a bindless descriptor set (VK_EXT_descriptor_indexing).
pub struct RuntimeBindlessDescriptorSet {
    /// Ghost model of the bindless descriptor set state.
    pub state: Ghost<BindlessDescriptorSetState>,
}

impl View for RuntimeBindlessDescriptorSet {
    type V = BindlessDescriptorSetState;
    open spec fn view(&self) -> BindlessDescriptorSetState { self.state@ }
}

/// Well-formedness of the runtime bindless descriptor set.
pub open spec fn runtime_bindless_wf(set: &RuntimeBindlessDescriptorSet) -> bool {
    bindless_set_well_formed(set@)
}

/// Exec: create a bindless descriptor set from ghost state.
pub fn create_bindless_set_exec(
    set_state: Ghost<BindlessDescriptorSetState>,
) -> (out: RuntimeBindlessDescriptorSet)
    requires bindless_set_well_formed(set_state@),
    ensures
        out@ == set_state@,
        runtime_bindless_wf(&out),
{
    RuntimeBindlessDescriptorSet { state: set_state }
}

} // verus!
