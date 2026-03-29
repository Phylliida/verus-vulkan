use vstd::prelude::*;
use crate::surface::*;

verus! {

///  Runtime wrapper for a VkSurfaceKHR.
pub struct RuntimeSurface {
    ///  Opaque handle (maps to VkSurfaceKHR).
    pub handle: u64,
    ///  Ghost model of the surface state.
    pub state: Ghost<SurfaceState>,
}

impl View for RuntimeSurface {
    type V = SurfaceState;
    open spec fn view(&self) -> SurfaceState { self.state@ }
}

///  Well-formedness of the runtime surface.
pub open spec fn runtime_surface_wf(s: &RuntimeSurface) -> bool {
    surface_well_formed(s@)
}

///  Surface is alive.
pub open spec fn runtime_surface_alive(s: &RuntimeSurface) -> bool {
    s@.alive
}

///  Proof: a well-formed runtime surface is alive.
pub proof fn lemma_runtime_surface_wf_alive(s: &RuntimeSurface)
    requires runtime_surface_wf(s),
    ensures s@.alive,
{
}

} //  verus!
