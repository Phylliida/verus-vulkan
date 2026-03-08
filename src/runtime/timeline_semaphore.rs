use vstd::prelude::*;
use crate::timeline_semaphore::*;
use crate::sync_token::*;

verus! {

/// Runtime wrapper for a Vulkan timeline semaphore.
pub struct RuntimeTimelineSemaphore {
    /// Opaque handle (maps to VkSemaphore with timeline type).
    pub handle: u64,
    /// Ghost model of the timeline semaphore state.
    pub state: Ghost<TimelineSemaphoreState>,
}

impl View for RuntimeTimelineSemaphore {
    type V = TimelineSemaphoreState;
    open spec fn view(&self) -> TimelineSemaphoreState { self.state@ }
}

// ── Well-formedness & Query Specs ───────────────────────────────────────

/// Well-formedness of the runtime timeline semaphore.
pub open spec fn runtime_timeline_wf(sem: &RuntimeTimelineSemaphore) -> bool {
    timeline_well_formed(sem@)
}

/// Current counter value.
pub open spec fn timeline_counter(sem: &RuntimeTimelineSemaphore) -> nat {
    sem@.counter
}

/// Whether there are pending signals.
pub open spec fn timeline_has_pending_signal(sem: &RuntimeTimelineSemaphore) -> bool {
    sem@.pending_signals.len() > 0
}

/// Whether there are pending waits.
pub open spec fn timeline_has_pending_wait(sem: &RuntimeTimelineSemaphore) -> bool {
    sem@.pending_waits.len() > 0
}

/// Whether a signal at the given value would advance the counter.
pub open spec fn signal_would_advance(
    sem: &RuntimeTimelineSemaphore,
    value: nat,
) -> bool {
    signal_value_valid(sem@, value)
}

/// Whether a wait at the given value is already satisfied.
pub open spec fn wait_would_complete(
    sem: &RuntimeTimelineSemaphore,
    value: nat,
) -> bool {
    wait_satisfied(sem@, value)
}

/// Whether the semaphore is alive.
pub open spec fn timeline_alive(sem: &RuntimeTimelineSemaphore) -> bool {
    sem@.alive
}

/// Semaphore ID.
pub open spec fn timeline_id(sem: &RuntimeTimelineSemaphore) -> nat {
    sem@.id
}

/// All pending signals have been resolved.
pub open spec fn all_signals_resolved(sem: &RuntimeTimelineSemaphore) -> bool {
    sem@.pending_signals == Set::<nat>::empty()
}

/// All pending waits have been satisfied.
pub open spec fn all_waits_satisfied(sem: &RuntimeTimelineSemaphore) -> bool {
    sem@.pending_waits == Set::<nat>::empty()
}

// ── Exec Functions ──────────────────────────────────────────────────────

/// Exec: create a timeline semaphore with initial value.
pub fn create_timeline_semaphore_exec(
    handle: u64,
    id: Ghost<nat>,
    initial_value: u64,
) -> (out: RuntimeTimelineSemaphore)
    ensures
        out@ == initial_timeline(id@, initial_value as nat),
        runtime_timeline_wf(&out),
{
    proof { lemma_initial_well_formed(id@, initial_value as nat); }
    RuntimeTimelineSemaphore {
        handle,
        state: Ghost(initial_timeline(id@, initial_value as nat)),
    }
}

/// Exec: destroy a timeline semaphore.
/// Caller must prove no pending GPU work references this semaphore and exclusive access.
pub fn destroy_timeline_semaphore_exec(
    sem: &mut RuntimeTimelineSemaphore,
    thread: Ghost<ThreadId>,
    reg: Ghost<TokenRegistry>,
)
    requires
        runtime_timeline_wf(&*old(sem)),
        old(sem)@.pending_signals == Set::<nat>::empty(),
        old(sem)@.pending_waits == Set::<nat>::empty(),
        holds_exclusive(reg@, old(sem).handle as nat, thread@),
    ensures
        !sem@.alive,
        sem@.id == old(sem)@.id,
{
    sem.state = Ghost(TimelineSemaphoreState {
        alive: false,
        ..sem.state@
    });
}

/// Exec: submit a signal operation (pending until GPU completes).
/// Caller must prove exclusive access to the timeline semaphore.
pub fn signal_timeline_exec(
    sem: &mut RuntimeTimelineSemaphore,
    value: u64,
    thread: Ghost<ThreadId>,
    reg: Ghost<TokenRegistry>,
)
    requires
        runtime_timeline_wf(&*old(sem)),
        signal_value_valid(old(sem)@, value as nat),
        holds_exclusive(reg@, old(sem).handle as nat, thread@),
    ensures
        sem@ == submit_signal(old(sem)@, value as nat),
{
    sem.state = Ghost(submit_signal(sem.state@, value as nat));
}

/// Exec: submit a wait operation (pending until value reached).
/// Caller must prove exclusive access to the timeline semaphore.
pub fn wait_timeline_exec(
    sem: &mut RuntimeTimelineSemaphore,
    value: u64,
    thread: Ghost<ThreadId>,
    reg: Ghost<TokenRegistry>,
)
    requires
        runtime_timeline_wf(&*old(sem)),
        holds_exclusive(reg@, old(sem).handle as nat, thread@),
    ensures
        sem@ == submit_wait(old(sem)@, value as nat),
{
    sem.state = Ghost(submit_wait(sem.state@, value as nat));
}

/// Exec: get current counter value (ghost query).
pub fn get_counter_value_exec(sem: &RuntimeTimelineSemaphore) -> (out: Ghost<nat>)
    requires runtime_timeline_wf(sem),
    ensures out@ == sem@.counter,
{
    Ghost(sem.state@.counter)
}

/// Exec: complete a pending signal (advances counter).
/// Caller must prove exclusive access to the timeline semaphore.
pub fn complete_signal_exec(
    sem: &mut RuntimeTimelineSemaphore,
    value: u64,
    thread: Ghost<ThreadId>,
    reg: Ghost<TokenRegistry>,
)
    requires
        runtime_timeline_wf(&*old(sem)),
        old(sem)@.pending_signals.contains(value as nat),
        signal_value_valid(old(sem)@, value as nat),
        holds_exclusive(reg@, old(sem).handle as nat, thread@),
    ensures
        sem@ == complete_signal(old(sem)@, value as nat),
        sem@.counter == value as nat,
{
    sem.state = Ghost(complete_signal(sem.state@, value as nat));
}

/// Exec: wait for multiple timeline semaphores (ghost-level batch wait).
/// Caller must prove all semaphores are well-formed.
pub fn wait_multiple_exec(
    sems: Ghost<Seq<TimelineSemaphoreState>>,
    values: Ghost<Seq<nat>>,
) -> (result: Ghost<bool>)
    requires
        sems@.len() == values@.len(),
        forall|i: int| 0 <= i < sems@.len()
            ==> timeline_well_formed(#[trigger] sems@[i]),
    ensures
        result@ ==> forall|i: int| 0 <= i < sems@.len()
            ==> wait_satisfied(#[trigger] sems@[i], values@[i]),
{
    Ghost(
        forall|i: int| 0 <= i < sems@.len()
            ==> wait_satisfied(#[trigger] sems@[i], values@[i])
    )
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// Created timeline semaphore is well-formed.
pub proof fn lemma_create_timeline_wf(id: nat, initial_value: nat)
    ensures runtime_timeline_wf(&RuntimeTimelineSemaphore {
        handle: 0,
        state: Ghost(initial_timeline(id, initial_value)),
    }),
{
    lemma_initial_well_formed(id, initial_value);
}

/// After completing a signal, the counter advances.
pub proof fn lemma_signal_advances_counter(
    sem: &RuntimeTimelineSemaphore,
    value: nat,
)
    requires
        runtime_timeline_wf(sem),
        signal_value_valid(sem@, value),
    ensures
        complete_signal(sem@, value).counter == value,
        complete_signal(sem@, value).counter > sem@.counter,
{
    crate::timeline_semaphore::lemma_signal_advances_counter(sem@, value);
}

/// After completing a signal, waits <= that value are satisfied.
pub proof fn lemma_wait_satisfied_after_signal(
    sem: &RuntimeTimelineSemaphore,
    signal_value: nat,
    wait_value: nat,
)
    requires
        runtime_timeline_wf(sem),
        signal_value_valid(sem@, signal_value),
        wait_value <= signal_value,
    ensures
        wait_satisfied(complete_signal(sem@, signal_value), wait_value),
{
    lemma_signal_satisfies_earlier_waits(sem@, signal_value, wait_value);
}

/// Signal values must be monotonically increasing.
pub proof fn lemma_signal_monotone(
    sem: &RuntimeTimelineSemaphore,
    v1: nat,
    v2: nat,
)
    requires
        runtime_timeline_wf(sem),
        signal_value_valid(sem@, v1),
        v2 > v1,
    ensures
        signal_value_valid(complete_signal(sem@, v1), v2),
{
    lemma_double_signal_ordering(sem@, v1, v2);
}

/// Counter is non-decreasing through signal operations.
pub proof fn lemma_counter_non_decreasing(
    sem: &RuntimeTimelineSemaphore,
    value: nat,
)
    requires
        runtime_timeline_wf(sem),
        signal_value_valid(sem@, value),
    ensures
        complete_signal(sem@, value).counter >= sem@.counter,
{
    crate::timeline_semaphore::lemma_signal_advances_counter(sem@, value);
}

/// Destroying makes the semaphore not alive and breaks well-formedness.
pub proof fn lemma_destroy_invalidates(sem: &RuntimeTimelineSemaphore)
    requires runtime_timeline_wf(sem),
    ensures ({
        let destroyed = TimelineSemaphoreState { alive: false, ..sem@ };
        !destroyed.alive
        && !timeline_well_formed(destroyed)
        && destroyed.counter == sem@.counter
        && destroyed.id == sem@.id
        && destroyed.pending_signals == sem@.pending_signals
        && destroyed.pending_waits == sem@.pending_waits
    }),
{
}

/// Completing a signal resolves pending waits at or below the signal value.
pub proof fn lemma_signal_resolves_pending_waits(
    sem: &RuntimeTimelineSemaphore,
    signal_value: nat,
    wait_value: nat,
)
    requires
        runtime_timeline_wf(sem),
        signal_value_valid(sem@, signal_value),
        sem@.pending_waits.contains(wait_value),
        wait_value <= signal_value,
    ensures
        !complete_signal(sem@, signal_value).pending_waits.contains(wait_value),
{
    let after = complete_signal(sem@, signal_value);
    // pending_waits after = { w | old pending && w > signal_value }
    // wait_value <= signal_value, so wait_value is removed
}

/// Pending signals are bounded above the counter.
pub proof fn lemma_pending_signals_bounded(
    sem: &RuntimeTimelineSemaphore,
    s: nat,
)
    requires
        runtime_timeline_wf(sem),
        sem@.pending_signals.contains(s),
    ensures
        s > sem@.counter,
{
    // From timeline_well_formed: all pending signals > counter
}

/// Wait value ≤ signal value after signal completes.
pub proof fn lemma_wait_value_leq_signal(
    sem: &RuntimeTimelineSemaphore,
    signal_value: nat,
    wait_value: nat,
)
    requires
        runtime_timeline_wf(sem),
        signal_value_valid(sem@, signal_value),
        wait_value <= signal_value,
    ensures
        wait_satisfied(complete_signal(sem@, signal_value), wait_value),
{
    lemma_signal_satisfies_earlier_waits(sem@, signal_value, wait_value);
}

/// Composing multiple waits: if all individual waits are satisfied, the batch is satisfied.
pub proof fn lemma_multiple_wait_composition(
    sems: Seq<TimelineSemaphoreState>,
    values: Seq<nat>,
)
    requires
        sems.len() == values.len(),
        forall|i: int| 0 <= i < sems.len()
            ==> wait_satisfied(#[trigger] sems[i], values[i]),
    ensures
        forall|i: int| 0 <= i < sems.len()
            ==> #[trigger] sems[i].counter >= values[i],
{
}

} // verus!
