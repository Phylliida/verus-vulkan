use vstd::prelude::*;

verus! {

//  ── Types ────────────────────────────────────────────────────────────

///  Ghost model for a VkSurfaceKHR object.
///  Surface is the WSI bridge between windowing system and Vulkan.
///  Intentionally minimal — the surface is opaque to the application after creation.
pub struct SurfaceState {
    ///  Unique identifier.
    pub id: nat,
    ///  Whether this surface is alive (not destroyed).
    pub alive: bool,
}

//  ── Spec Functions ───────────────────────────────────────────────────

///  A surface is well-formed iff it is alive.
pub open spec fn surface_well_formed(s: SurfaceState) -> bool {
    s.alive
}

///  Ghost update: destroy a surface.
pub open spec fn destroy_surface_ghost(s: SurfaceState) -> SurfaceState
    recommends s.alive,
{
    SurfaceState { alive: false, ..s }
}

///  A surface is alive.
pub open spec fn surface_alive(s: SurfaceState) -> bool {
    s.alive
}

//  ── Proofs ───────────────────────────────────────────────────────────

///  A freshly created surface (alive: true) is alive.
pub proof fn lemma_create_surface_alive(id: nat)
    ensures surface_alive(SurfaceState { id, alive: true }),
{
}

///  After destroying, a surface is not alive.
pub proof fn lemma_destroy_surface_not_alive(s: SurfaceState)
    requires s.alive,
    ensures !destroy_surface_ghost(s).alive,
{
}

///  Destroying a surface preserves its id.
pub proof fn lemma_destroy_surface_preserves_id(s: SurfaceState)
    ensures destroy_surface_ghost(s).id == s.id,
{
}

} //  verus!
