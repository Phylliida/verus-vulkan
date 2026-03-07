use vstd::prelude::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// Ghost state for a Vulkan timeline semaphore.
///
/// Timeline semaphores have a monotonically increasing u64 counter.
/// Signal operations set the counter to a specified value (must be
/// strictly greater than current). Wait operations block until the
/// counter is >= the specified value.
pub struct TimelineSemaphoreState {
    pub id: nat,
    /// Current counter value.
    pub counter: nat,
    /// Pending signal values (from submitted but not yet completed work).
    pub pending_signals: Set<nat>,
    /// Pending wait values (from submitted but not yet started work).
    pub pending_waits: Set<nat>,
    /// Whether this semaphore is alive.
    pub alive: bool,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// Create a fresh timeline semaphore with initial value.
pub open spec fn initial_timeline(id: nat, initial_value: nat) -> TimelineSemaphoreState {
    TimelineSemaphoreState {
        id,
        counter: initial_value,
        pending_signals: Set::<nat>::empty(),
        pending_waits: Set::<nat>::empty(),
        alive: true,
    }
}

/// Whether a signal value is valid: must be strictly greater than current counter.
pub open spec fn signal_value_valid(
    sem: TimelineSemaphoreState,
    value: nat,
) -> bool {
    value > sem.counter
}

/// Whether a wait is already satisfied by the current counter.
pub open spec fn wait_satisfied(
    sem: TimelineSemaphoreState,
    value: nat,
) -> bool {
    sem.counter >= value
}

/// Submit a signal operation (goes pending until GPU completes it).
pub open spec fn submit_signal(
    sem: TimelineSemaphoreState,
    value: nat,
) -> TimelineSemaphoreState {
    TimelineSemaphoreState {
        pending_signals: sem.pending_signals.insert(value),
        ..sem
    }
}

/// Submit a wait operation (goes pending until GPU starts it).
pub open spec fn submit_wait(
    sem: TimelineSemaphoreState,
    value: nat,
) -> TimelineSemaphoreState {
    TimelineSemaphoreState {
        pending_waits: sem.pending_waits.insert(value),
        ..sem
    }
}

/// Complete a signal: advances the counter to the signaled value.
pub open spec fn complete_signal(
    sem: TimelineSemaphoreState,
    value: nat,
) -> TimelineSemaphoreState {
    TimelineSemaphoreState {
        counter: value,
        pending_signals: sem.pending_signals.remove(value),
        // Remove all waits satisfied by this signal
        pending_waits: Set::new(
            |w: nat| sem.pending_waits.contains(w) && w > value,
        ),
        ..sem
    }
}

/// Host-side wait: blocks until counter >= value.
pub open spec fn host_wait(
    sem: TimelineSemaphoreState,
    value: nat,
) -> TimelineSemaphoreState {
    // Host wait doesn't change state — it just blocks until the condition is met.
    // After the wait returns, we know counter >= value.
    sem
}

/// No deadlock: every pending wait has a pending or completed signal >= its value.
pub open spec fn no_deadlock(sem: TimelineSemaphoreState) -> bool {
    forall|w: nat| sem.pending_waits.contains(w) ==>
        sem.counter >= w
        || exists|s: nat| #[trigger] sem.pending_signals.contains(s) && s >= w
}

/// The semaphore is well-formed: counter is consistent with signals.
pub open spec fn timeline_well_formed(sem: TimelineSemaphoreState) -> bool {
    sem.alive
    // All pending signals must be strictly greater than current counter
    && (forall|s: nat| sem.pending_signals.contains(s) ==> s > sem.counter)
    // No deadlock
    && no_deadlock(sem)
}

/// Monotonicity: a signal value must be greater than all previous pending signals' values
/// that have already completed.
pub open spec fn signal_monotonic(
    sem: TimelineSemaphoreState,
    value: nat,
) -> bool {
    value > sem.counter
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// A fresh timeline semaphore is well-formed.
pub proof fn lemma_initial_well_formed(id: nat, initial_value: nat)
    ensures
        timeline_well_formed(initial_timeline(id, initial_value)),
{
    let sem = initial_timeline(id, initial_value);
    assert(sem.alive);
    assert(sem.pending_signals == Set::<nat>::empty());
    assert(sem.pending_waits == Set::<nat>::empty());
}

/// After completing a signal, the counter has advanced.
pub proof fn lemma_signal_advances_counter(
    sem: TimelineSemaphoreState,
    value: nat,
)
    requires
        signal_value_valid(sem, value),
    ensures
        complete_signal(sem, value).counter == value,
        complete_signal(sem, value).counter > sem.counter,
{
}

/// A completed signal satisfies all waits <= the signaled value.
pub proof fn lemma_signal_satisfies_earlier_waits(
    sem: TimelineSemaphoreState,
    signal_value: nat,
    wait_value: nat,
)
    requires
        signal_value_valid(sem, signal_value),
        wait_value <= signal_value,
    ensures
        wait_satisfied(complete_signal(sem, signal_value), wait_value),
{
}

/// Host wait returns only when the counter is sufficient.
pub proof fn lemma_host_wait_ensures_counter(
    sem: TimelineSemaphoreState,
    value: nat,
)
    requires wait_satisfied(sem, value),
    ensures
        host_wait(sem, value).counter >= value,
{
}

/// Submitting a signal preserves existing pending waits.
pub proof fn lemma_submit_signal_preserves_waits(
    sem: TimelineSemaphoreState,
    signal_value: nat,
    wait_value: nat,
)
    requires sem.pending_waits.contains(wait_value),
    ensures
        submit_signal(sem, signal_value).pending_waits.contains(wait_value),
{
}

/// Submitting a wait preserves the counter.
pub proof fn lemma_submit_wait_preserves_counter(
    sem: TimelineSemaphoreState,
    value: nat,
)
    ensures
        submit_wait(sem, value).counter == sem.counter,
{
}

/// If the counter already satisfies a wait, the wait is immediately satisfied.
pub proof fn lemma_counter_ge_wait_satisfied(
    sem: TimelineSemaphoreState,
    value: nat,
)
    requires sem.counter >= value,
    ensures wait_satisfied(sem, value),
{
}

/// A signal followed by another signal must maintain strict ordering.
pub proof fn lemma_double_signal_ordering(
    sem: TimelineSemaphoreState,
    v1: nat,
    v2: nat,
)
    requires
        signal_value_valid(sem, v1),
        v2 > v1,
    ensures
        signal_value_valid(complete_signal(sem, v1), v2),
{
}

} // verus!
