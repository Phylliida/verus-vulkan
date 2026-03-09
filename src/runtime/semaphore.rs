use vstd::prelude::*;
use crate::semaphore::*;
use crate::resource::*;
use crate::sync::*;
use crate::lifetime::*;
use crate::sync_token::*;
use super::device::RuntimeDevice;

verus! {

/// Runtime wrapper for a Vulkan semaphore.
pub struct RuntimeSemaphore {
    /// Opaque handle (maps to VkSemaphore).
    pub handle: u64,
    /// Ghost model of the semaphore state.
    pub state: Ghost<SemaphoreState>,
}

impl View for RuntimeSemaphore {
    type V = SemaphoreState;
    open spec fn view(&self) -> SemaphoreState { self.state@ }
}

/// Well-formedness of the runtime semaphore.
pub open spec fn runtime_semaphore_wf(sem: &RuntimeSemaphore) -> bool {
    semaphore_well_formed(sem@)
}

/// Exec: create a binary semaphore.
pub fn create_semaphore_exec(id: Ghost<nat>) -> (out: RuntimeSemaphore)
    ensures
        out@ == create_semaphore_ghost(id@),
        runtime_semaphore_wf(&out),
{
    RuntimeSemaphore {
        handle: 0,
        state: Ghost(create_semaphore_ghost(id@)),
    }
}

/// Exec: signal a semaphore (marks as signaled with resource states).
/// Caller must prove exclusive access to the semaphore.
pub fn signal_semaphore_exec(
    sem: &mut RuntimeSemaphore,
    states: Ghost<Map<ResourceId, SyncState>>,
    referenced_resources: Ghost<Set<ResourceId>>,
    thread: Ghost<ThreadId>,
    reg: Ghost<TokenRegistry>,
)
    requires
        runtime_semaphore_wf(&*old(sem)),
        holds_exclusive(reg@, old(sem)@.id, thread@),
        // States must only cover referenced resources
        forall|r: ResourceId| states@.contains_key(r)
            ==> referenced_resources@.contains(r),
        // Each state must be self-consistent
        forall|r: ResourceId| states@.contains_key(r)
            ==> (#[trigger] states@[r]).resource == r,
    ensures
        sem@ == signal_semaphore_ghost(old(sem)@, states@),
{
    sem.state = Ghost(signal_semaphore_ghost(sem.state@, states@));
}

/// Exec: wait on a semaphore (marks as unsignaled/consumed).
/// Caller must prove exclusive access to the semaphore.
pub fn wait_semaphore_exec(
    sem: &mut RuntimeSemaphore,
    thread: Ghost<ThreadId>,
    reg: Ghost<TokenRegistry>,
)
    requires
        runtime_semaphore_wf(&*old(sem)),
        old(sem)@.signaled,
        holds_exclusive(reg@, old(sem)@.id, thread@),
    ensures
        sem@ == wait_semaphore_ghost(old(sem)@),
{
    sem.state = Ghost(wait_semaphore_ghost(sem.state@));
}

/// Exec: destroy a semaphore.
/// Caller must prove no pending submission signals this semaphore and exclusive access.
/// Note: Vulkan allows destroying signaled semaphores (unlike fences).
pub fn destroy_semaphore_exec(
    sem: &mut RuntimeSemaphore,
    dev: &RuntimeDevice,
    thread: Ghost<ThreadId>,
    reg: Ghost<TokenRegistry>,
)
    requires
        runtime_semaphore_wf(&*old(sem)),
        semaphore_not_pending(old(sem)@.id, dev@.pending_submissions),
        holds_exclusive(reg@, old(sem)@.id, thread@),
    ensures
        sem@ == destroy_semaphore_ghost(old(sem)@),
        !sem@.alive,
{
    sem.state = Ghost(destroy_semaphore_ghost(sem.state@));
}

// ── Extended Specs & Proofs ──────────────────────────────────────────

/// Semaphore is signaled.
pub open spec fn sem_is_signaled(sem: &RuntimeSemaphore) -> bool {
    sem@.signaled
}

/// Semaphore is alive.
pub open spec fn sem_alive(sem: &RuntimeSemaphore) -> bool {
    sem@.alive
}

/// Proof: created semaphore is unsignaled.
pub proof fn lemma_create_unsignaled(id: Ghost<nat>)
    ensures !create_semaphore_ghost(id@).signaled,
{
    lemma_create_semaphore_unsignaled(id@);
}

/// Proof: signal then wait roundtrip.
pub proof fn lemma_signal_wait_roundtrip_rt(
    sem: &RuntimeSemaphore,
    states: Ghost<Map<ResourceId, SyncState>>,
)
    requires
        runtime_semaphore_wf(sem),
        !sem@.signaled,
    ensures ({
        let signaled = signal_semaphore_ghost(sem@, states@);
        !wait_semaphore_ghost(signaled).signaled
    }),
{
    lemma_signal_wait_roundtrip(sem@, states@);
}

/// Proof: signal preserves alive.
pub proof fn lemma_signal_alive_rt(
    sem: &RuntimeSemaphore,
    states: Ghost<Map<ResourceId, SyncState>>,
)
    requires runtime_semaphore_wf(sem),
    ensures signal_semaphore_ghost(sem@, states@).alive,
{
    lemma_signal_preserves_alive(sem@, states@);
}

/// Proof: wait preserves alive.
pub proof fn lemma_wait_alive_rt(sem: &RuntimeSemaphore)
    requires
        runtime_semaphore_wf(sem),
        sem@.signaled,
    ensures wait_semaphore_ghost(sem@).alive,
{
    lemma_wait_preserves_alive(sem@);
}

} // verus!
