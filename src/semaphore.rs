use vstd::prelude::*;
use crate::resource::*;
use crate::sync::*;
use crate::lifetime::*;

verus! {

/// Ghost state for a Vulkan semaphore.
///
/// Semaphores provide GPU-GPU synchronization between queue submissions.
/// When signaled, they carry ghost resource states that are transferred
/// to the waiting submission (cross-submission state transfer).
pub struct SemaphoreState {
    /// Unique semaphore identifier.
    pub id: nat,
    /// Whether the semaphore is currently signaled.
    pub signaled: bool,
    /// Ghost resource states deposited by the signaling submission.
    /// Consumed (cleared) when a wait operation occurs.
    pub resource_states: Map<ResourceId, SyncState>,
    /// Whether the semaphore has not been destroyed.
    pub alive: bool,
}

/// A semaphore is well-formed if it is alive.
pub open spec fn semaphore_well_formed(sem: SemaphoreState) -> bool {
    sem.alive
}

/// Create a fresh unsignaled semaphore with no resource states.
pub open spec fn create_semaphore_ghost(id: nat) -> SemaphoreState {
    SemaphoreState {
        id,
        signaled: false,
        resource_states: Map::empty(),
        alive: true,
    }
}

/// Ghost update: signal the semaphore and deposit resource states.
pub open spec fn signal_semaphore_ghost(
    sem: SemaphoreState,
    states: Map<ResourceId, SyncState>,
) -> SemaphoreState {
    SemaphoreState {
        signaled: true,
        resource_states: states,
        ..sem
    }
}

/// Ghost update: wait on the semaphore, consuming its signal and clearing states.
pub open spec fn wait_semaphore_ghost(sem: SemaphoreState) -> SemaphoreState {
    SemaphoreState {
        signaled: false,
        resource_states: Map::empty(),
        ..sem
    }
}

/// Ghost update: destroy the semaphore.
pub open spec fn destroy_semaphore_ghost(sem: SemaphoreState) -> SemaphoreState {
    SemaphoreState {
        alive: false,
        ..sem
    }
}

/// No pending (uncompleted) submission signals this semaphore.
pub open spec fn semaphore_not_pending(
    sem_id: nat,
    pending_submissions: Seq<SubmissionRecord>,
) -> bool {
    forall|i: int| 0 <= i < pending_submissions.len()
        ==> !pending_submissions[i].completed
            ==> forall|j: int| 0 <= j < (#[trigger] pending_submissions[i]).signal_semaphores.len()
                ==> pending_submissions[i].signal_semaphores[j] != sem_id
}

// ── Lemmas ──────────────────────────────────────────────────────────────

/// A freshly created semaphore is not signaled.
pub proof fn lemma_create_semaphore_unsignaled(id: nat)
    ensures !create_semaphore_ghost(id).signaled,
{
}

/// After signaling, the semaphore is signaled.
pub proof fn lemma_signal_makes_signaled(
    sem: SemaphoreState,
    states: Map<ResourceId, SyncState>,
)
    ensures signal_semaphore_ghost(sem, states).signaled,
{
}

/// After waiting, the semaphore is not signaled.
pub proof fn lemma_wait_consumes_signal(sem: SemaphoreState)
    ensures !wait_semaphore_ghost(sem).signaled,
{
}

/// A signaled semaphore holds the deposited resource states.
pub proof fn lemma_signal_carries_states(
    sem: SemaphoreState,
    states: Map<ResourceId, SyncState>,
)
    ensures signal_semaphore_ghost(sem, states).resource_states == states,
{
}

/// A freshly created semaphore is well-formed.
pub proof fn lemma_create_semaphore_well_formed(id: nat)
    ensures semaphore_well_formed(create_semaphore_ghost(id)),
{
}

/// Signal → wait roundtrip returns to unsignaled with empty states.
pub proof fn lemma_signal_wait_roundtrip(
    sem: SemaphoreState, states: Map<ResourceId, SyncState>,
)
    ensures ({
        let signaled = signal_semaphore_ghost(sem, states);
        let waited = wait_semaphore_ghost(signaled);
        !waited.signaled && waited.resource_states == Map::<ResourceId, SyncState>::empty()
    }),
{
}

/// Signaling preserves alive status.
pub proof fn lemma_signal_preserves_alive(
    sem: SemaphoreState, states: Map<ResourceId, SyncState>,
)
    requires sem.alive,
    ensures signal_semaphore_ghost(sem, states).alive,
{
}

/// Waiting preserves alive status.
pub proof fn lemma_wait_preserves_alive(sem: SemaphoreState)
    requires sem.alive,
    ensures wait_semaphore_ghost(sem).alive,
{
}

} // verus!
