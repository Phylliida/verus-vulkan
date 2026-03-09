use vstd::prelude::*;
use crate::lifetime::*;
use crate::sampler::*;
use crate::sync_token::*;
use super::device::RuntimeDevice;

verus! {

/// Runtime wrapper for a Vulkan sampler.
pub struct RuntimeSampler {
    /// Opaque handle (maps to VkSampler).
    pub handle: u64,
    /// Ghost model of the sampler state.
    pub state: Ghost<SamplerState>,
}

impl View for RuntimeSampler {
    type V = SamplerState;
    open spec fn view(&self) -> SamplerState { self.state@ }
}

/// Well-formedness of the runtime sampler.
pub open spec fn runtime_sampler_wf(s: &RuntimeSampler) -> bool {
    sampler_well_formed(s@)
}

/// Exec: create a sampler with the default configuration.
pub fn create_default_sampler_exec(id: Ghost<nat>) -> (out: RuntimeSampler)
    ensures
        out@ == default_sampler(id@),
        runtime_sampler_wf(&out),
{
    proof { lemma_default_sampler_well_formed(id@); }
    RuntimeSampler {
        handle: 0,
        state: Ghost(default_sampler(id@)),
    }
}

/// Exec: create a sampler from a ghost state.
pub fn create_sampler_exec(
    ss: Ghost<SamplerState>,
) -> (out: RuntimeSampler)
    requires sampler_well_formed(ss@),
    ensures
        out@ == ss@,
        runtime_sampler_wf(&out),
{
    RuntimeSampler {
        handle: 0,
        state: ss,
    }
}

/// Exec: destroy a sampler.
/// Caller must prove exclusive access.
pub fn destroy_sampler_exec(
    s: &mut RuntimeSampler,
    dev: &RuntimeDevice,
    thread: Ghost<ThreadId>,
    reg: Ghost<TokenRegistry>,
)
    requires
        runtime_sampler_wf(&*old(s)),
        // All pending submissions must be completed
        forall|i: int| 0 <= i < dev@.pending_submissions.len()
            ==> (#[trigger] dev@.pending_submissions[i]).completed,
        holds_exclusive(reg@, old(s)@.id, thread@),
    ensures
        s@ == destroy_sampler_ghost(old(s)@),
        !s@.alive,
{
    s.state = Ghost(destroy_sampler_ghost(s.state@));
}

// ── Extended Specs & Proofs ──────────────────────────────────────────

/// Sampler is alive.
pub open spec fn sampler_alive(s: &RuntimeSampler) -> bool {
    s@.alive
}

/// Proof: creating a default sampler produces an alive sampler.
pub proof fn lemma_create_default_sampler_alive(id: Ghost<nat>)
    ensures sampler_alive(&RuntimeSampler {
        handle: 0,
        state: Ghost(default_sampler(id@)),
    }),
{
}

/// Proof: destroying a sampler preserves its id.
pub proof fn lemma_destroy_sampler_preserves_id_rt(s: &RuntimeSampler)
    requires runtime_sampler_wf(s),
    ensures destroy_sampler_ghost(s@).id == s@.id,
{
}

} // verus!
