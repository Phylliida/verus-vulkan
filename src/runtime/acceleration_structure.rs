use vstd::prelude::*;
use crate::acceleration_structure::*;
use crate::lifetime::*;
use crate::sync_token::*;
use super::device::RuntimeDevice;

verus! {

/// Runtime wrapper for a VkAccelerationStructureKHR.
pub struct RuntimeAccelerationStructure {
    /// Opaque handle (maps to VkAccelerationStructureKHR).
    pub handle: u64,
    /// Ghost model of the acceleration structure state.
    pub state: Ghost<AccelerationStructureState>,
}

impl View for RuntimeAccelerationStructure {
    type V = AccelerationStructureState;
    open spec fn view(&self) -> AccelerationStructureState { self.state@ }
}

/// Well-formedness of the runtime acceleration structure.
pub open spec fn runtime_as_wf(as_obj: &RuntimeAccelerationStructure) -> bool {
    as_well_formed(as_obj@)
}

/// Exec: create an acceleration structure from ghost state.
pub fn create_as_exec(
    as_state: Ghost<AccelerationStructureState>,
) -> (out: RuntimeAccelerationStructure)
    requires as_well_formed(as_state@),
    ensures
        out@ == as_state@,
        runtime_as_wf(&out),
{
    RuntimeAccelerationStructure {
        handle: 0,
        state: as_state,
    }
}

/// Exec: destroy an acceleration structure.
pub fn destroy_as_exec(
    as_obj: &mut RuntimeAccelerationStructure,
    dev: &RuntimeDevice,
    thread: Ghost<ThreadId>,
    reg: Ghost<TokenRegistry>,
)
    requires
        runtime_as_wf(&*old(as_obj)),
        forall|i: int| 0 <= i < dev@.pending_submissions.len()
            ==> (#[trigger] dev@.pending_submissions[i]).completed,
        holds_exclusive(reg@, SyncObjectId::Handle(old(as_obj)@.id), thread@),
    ensures
        as_obj@ == destroy_as_ghost(old(as_obj)@),
        !as_obj@.alive,
{
    as_obj.state = Ghost(destroy_as_ghost(as_obj.state@));
}

/// Exec: build an acceleration structure.
pub fn build_as_exec(
    as_obj: &mut RuntimeAccelerationStructure,
    mode: Ghost<ASBuildMode>,
)
    requires
        runtime_as_wf(&*old(as_obj)),
    ensures
        as_obj@ == build_as_ghost(old(as_obj)@, mode@),
        runtime_as_wf(as_obj),
        as_obj@.built,
{
    proof {
        if blas_well_formed(as_obj.state@) {
            lemma_build_preserves_blas_well_formed(as_obj.state@, mode@);
        } else {
            lemma_build_preserves_tlas_well_formed(as_obj.state@, mode@);
        }
    }
    as_obj.state = Ghost(build_as_ghost(as_obj.state@, mode@));
}

/// Exec: compact an acceleration structure.
pub fn compact_as_exec(
    as_obj: &mut RuntimeAccelerationStructure,
)
    requires
        runtime_as_wf(&*old(as_obj)),
    ensures
        as_obj@ == compact_as_ghost(old(as_obj)@),
        runtime_as_wf(as_obj),
{
    proof {
        if blas_well_formed(as_obj.state@) {
            lemma_compact_preserves_blas_well_formed(as_obj.state@);
        } else {
            lemma_compact_preserves_tlas_well_formed(as_obj.state@);
        }
    }
    as_obj.state = Ghost(compact_as_ghost(as_obj.state@));
}

// ── Specs & Proofs ──────────────────────────────────────────────────

/// AS is alive.
pub open spec fn as_alive(as_obj: &RuntimeAccelerationStructure) -> bool {
    as_obj@.alive
}

/// AS has been built.
pub open spec fn as_built(as_obj: &RuntimeAccelerationStructure) -> bool {
    as_obj@.built
}

/// Proof: destroying preserves id.
pub proof fn lemma_destroy_as_preserves_id(as_obj: &RuntimeAccelerationStructure)
    requires runtime_as_wf(as_obj),
    ensures destroy_as_ghost(as_obj@).id == as_obj@.id,
{
}

/// Proof: building preserves id.
pub proof fn lemma_build_as_preserves_id(as_obj: &RuntimeAccelerationStructure, mode: ASBuildMode)
    requires runtime_as_wf(as_obj),
    ensures build_as_ghost(as_obj@, mode).id == as_obj@.id,
{
}

} // verus!
