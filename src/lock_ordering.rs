use vstd::prelude::*;
use crate::sync_token::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// A thread's currently held locks as a set of (object_id, level) pairs.
///
/// Unlike the old LIFO-stack model, this uses a Set — locks can be
/// released in any order. The ordering invariant only constrains
/// acquisition: you must acquire at a strictly higher level than
/// your current maximum.
///
/// This models the standard deadlock prevention technique: assign
/// a total order to lock types, acquire in increasing order.
pub struct HeldLocks {
    pub thread: ThreadId,
    /// Set of (object_id, lock_level) currently held.
    pub locks: Set<(nat, nat)>,
    /// The maximum level currently held (-1 if none).
    pub max_level: int,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// Lock level assignments for Vulkan object types.
/// Device < Queue < CommandPool < CommandBuffer < DescriptorPool < Fence < Semaphore
pub open spec fn device_level() -> nat { 0 }
pub open spec fn queue_level() -> nat { 1 }
pub open spec fn command_pool_level() -> nat { 2 }
pub open spec fn command_buffer_level() -> nat { 3 }
pub open spec fn descriptor_pool_level() -> nat { 4 }
pub open spec fn fence_level() -> nat { 5 }
pub open spec fn semaphore_level() -> nat { 6 }

/// Lock ordering invariant: all held locks have levels <= max_level,
/// and no two locks share the same level (strict per-level uniqueness).
pub open spec fn lock_order_valid(held: HeldLocks) -> bool {
    // All lock levels are <= max_level
    (forall|pair: (nat, nat)| held.locks.contains(pair)
        ==> (#[trigger] pair.1) as int <= held.max_level)
    // No two different objects at the same level
    && (forall|p1: (nat, nat), p2: (nat, nat)|
        held.locks.contains(p1) && held.locks.contains(p2)
        && p1.0 != p2.0
        ==> (#[trigger] p1.1) != (#[trigger] p2.1))
}

/// Can acquire a lock at the given level: must be strictly above max.
pub open spec fn can_acquire_at_level(
    held: HeldLocks,
    level: nat,
) -> bool {
    lock_order_valid(held)
    && level as int > held.max_level
}

/// Acquire a lock: add to the set and update max_level.
pub open spec fn acquire_lock(
    held: HeldLocks,
    object_id: nat,
    level: nat,
) -> HeldLocks {
    HeldLocks {
        locks: held.locks.insert((object_id, level)),
        max_level: level as int,
        ..held
    }
}

/// Release a specific lock (any order, not just LIFO).
pub open spec fn release_lock(
    held: HeldLocks,
    object_id: nat,
    level: nat,
) -> HeldLocks
    recommends held.locks.contains((object_id, level)),
{
    let new_locks = held.locks.remove((object_id, level));
    HeldLocks {
        locks: new_locks,
        // max_level stays the same or decreases — we keep it as an
        // upper bound (it's safe to overestimate)
        max_level: held.max_level,
        ..held
    }
}

/// No locks held.
pub open spec fn no_locks(thread: ThreadId) -> HeldLocks {
    HeldLocks {
        thread,
        locks: Set::empty(),
        max_level: -1int,
    }
}

/// A thread holds a specific object's lock.
pub open spec fn holds_lock_on(held: HeldLocks, object_id: nat) -> bool {
    exists|level: nat| held.locks.contains((object_id, level))
}

/// Two threads' held locks don't overlap (no shared objects).
pub open spec fn locks_non_overlapping(
    held1: HeldLocks,
    held2: HeldLocks,
) -> bool {
    forall|p1: (nat, nat), p2: (nat, nat)|
        held1.locks.contains(p1) && held2.locks.contains(p2)
        ==> (#[trigger] p1.0) != (#[trigger] p2.0)
}

/// A circular wait exists between two threads:
/// Thread 1 holds lock at level_a and wants level_b.
/// Thread 2 holds lock at level_b and wants level_a.
/// This requires level_b > level_a AND level_a > level_b — impossible.
pub open spec fn circular_wait_levels(
    level_a: nat,
    level_b: nat,
    max1: int,
    max2: int,
) -> bool {
    // Thread 1 holds something at level_a, max is at least level_a
    level_a as int <= max1
    // Thread 1 wants level_b: requires level_b > max1
    && level_b as int > max1
    // Thread 2 holds something at level_b, max is at least level_b
    && level_b as int <= max2
    // Thread 2 wants level_a: requires level_a > max2
    && level_a as int > max2
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// An empty lock set is trivially valid.
pub proof fn lemma_empty_locks_valid(thread: ThreadId)
    ensures lock_order_valid(no_locks(thread)),
{
}

/// Acquiring in order maintains the ordering invariant.
pub proof fn lemma_acquire_maintains_order(
    held: HeldLocks,
    object_id: nat,
    level: nat,
)
    requires can_acquire_at_level(held, level),
    ensures
        lock_order_valid(acquire_lock(held, object_id, level)),
{
    let new_held = acquire_lock(held, object_id, level);
    // All old locks had level <= old max_level < new level
    assert forall|pair: (nat, nat)|
        new_held.locks.contains(pair)
    implies (pair.1 as int) <= new_held.max_level by {
        if pair == (object_id, level) {
            // The new lock: level == new max_level
        } else {
            // Old lock: level <= old max_level < new level == new max_level
            assert(held.locks.contains(pair));
            assert((pair.1 as int) <= held.max_level);
        }
    }
    // No two different objects at the same level
    assert forall|p1: (nat, nat), p2: (nat, nat)|
        new_held.locks.contains(p1) && new_held.locks.contains(p2)
        && p1.0 != p2.0
    implies p1.1 != p2.1 by {
        if p1 == (object_id, level) {
            // p1 is new, p2 is old: old level <= old max < new level
            assert(held.locks.contains(p2));
            assert((p2.1 as int) <= held.max_level);
        } else if p2 == (object_id, level) {
            assert(held.locks.contains(p1));
            assert((p1.1 as int) <= held.max_level);
        } else {
            // Both old: from lock_order_valid(held)
        }
    }
}

/// After acquiring, the thread holds the lock.
pub proof fn lemma_acquire_holds(
    held: HeldLocks,
    object_id: nat,
    level: nat,
)
    ensures holds_lock_on(acquire_lock(held, object_id, level), object_id),
{
    let new_held = acquire_lock(held, object_id, level);
    assert(new_held.locks.contains((object_id, level)));
}

/// Non-overlapping lock sets: if thread 1 holds it, thread 2 doesn't.
pub proof fn lemma_non_overlapping_exclusive(
    held1: HeldLocks,
    held2: HeldLocks,
    object_id: nat,
    level: nat,
)
    requires
        locks_non_overlapping(held1, held2),
        held1.locks.contains((object_id, level)),
    ensures
        !holds_lock_on(held2, object_id),
{
    if holds_lock_on(held2, object_id) {
        let level2 = choose|l: nat| held2.locks.contains((object_id, l));
        let p1 = (object_id, level);
        let p2 = (object_id, level2);
        assert(held1.locks.contains(p1));
        assert(held2.locks.contains(p2));
        // Trigger: p1.0 != p2.0 but they're equal → contradiction
        assert(p1.0 == p2.0);
    }
}

/// Ordered locking prevents circular wait (deadlock freedom).
///
/// If thread 1 holds a lock at level_a (so max1 >= level_a) and
/// wants level_b (needs level_b > max1), while thread 2 holds
/// level_b (max2 >= level_b) and wants level_a (needs level_a > max2),
/// we'd need level_b > max1 >= level_a > max2 >= level_b — contradiction.
pub proof fn lemma_ordered_no_circular_wait(
    level_a: nat,
    level_b: nat,
    max1: int,
    max2: int,
)
    ensures
        !circular_wait_levels(level_a, level_b, max1, max2),
{
    // Proof by contradiction: if all four conditions hold,
    // level_b > max1 >= level_a > max2 >= level_b
    // implies level_b > level_b — impossible.
}

/// Releasing any lock preserves the ordering invariant.
/// (max_level is kept as an upper bound, so it remains valid.)
pub proof fn lemma_release_preserves_order(
    held: HeldLocks,
    object_id: nat,
    level: nat,
)
    requires
        held.locks.contains((object_id, level)),
        lock_order_valid(held),
    ensures
        lock_order_valid(release_lock(held, object_id, level)),
{
    let new_held = release_lock(held, object_id, level);
    assert forall|pair: (nat, nat)|
        new_held.locks.contains(pair)
    implies (pair.1 as int) <= new_held.max_level by {
        assert(held.locks.contains(pair));
    }
}

/// An empty lock set has no locks on any object.
pub proof fn lemma_no_locks_empty(thread: ThreadId, object_id: nat)
    ensures !holds_lock_on(no_locks(thread), object_id),
{
}

/// After acquiring, the new max_level equals the acquired level.
pub proof fn lemma_acquire_updates_max(
    held: HeldLocks, object_id: nat, level: nat,
)
    requires can_acquire_at_level(held, level),
    ensures acquire_lock(held, object_id, level).max_level == level as int,
{
}

/// Release preserves that the thread is the same.
pub proof fn lemma_release_preserves_thread(
    held: HeldLocks, object_id: nat, level: nat,
)
    requires held.locks.contains((object_id, level)),
    ensures release_lock(held, object_id, level).thread == held.thread,
{
}

/// After releasing, the released lock is no longer held.
pub proof fn lemma_release_removes_lock(
    held: HeldLocks, object_id: nat, level: nat,
)
    requires held.locks.contains((object_id, level)),
    ensures !release_lock(held, object_id, level).locks.contains((object_id, level)),
{
}

/// Two sequential acquisitions maintain order: first < second.
pub proof fn lemma_sequential_acquisitions_ordered(
    held: HeldLocks, obj1: nat, lv1: nat, obj2: nat, lv2: nat,
)
    requires
        can_acquire_at_level(held, lv1),
        can_acquire_at_level(acquire_lock(held, obj1, lv1), lv2),
    ensures lv1 < lv2,
{
    let mid = acquire_lock(held, obj1, lv1);
    assert(mid.max_level == lv1 as int);
    assert(lv2 as int > mid.max_level);
}

/// Can't acquire at a level already held (no re-entrant locks).
pub proof fn lemma_no_reentrant_acquisition(
    held: HeldLocks, object_id: nat, level: nat,
)
    requires
        lock_order_valid(held),
        held.locks.contains((object_id, level)),
    ensures !can_acquire_at_level(held, level),
{
    let pair = (object_id, level);
    // Trigger the forall in lock_order_valid: pair.1 as int <= max_level
    assert(pair.1 as int <= held.max_level);
    // So level as int > max_level is false → can_acquire is false
}

/// Acquiring then immediately releasing restores lock_order_valid.
pub proof fn lemma_acquire_release_roundtrip(
    held: HeldLocks, object_id: nat, level: nat,
)
    requires can_acquire_at_level(held, level),
    ensures lock_order_valid(
        release_lock(acquire_lock(held, object_id, level), object_id, level)
    ),
{
    let mid = acquire_lock(held, object_id, level);
    lemma_acquire_maintains_order(held, object_id, level);
    assert(mid.locks.contains((object_id, level)));
    lemma_release_preserves_order(mid, object_id, level);
}

/// Two threads following lock ordering can never form a circular wait.
/// This is the full Coffman deadlock prevention theorem:
/// if thread 1 holds at level_a and wants level_b, and thread 2 holds
/// at level_b and wants level_a, ordered locking makes this impossible.
pub proof fn lemma_ordered_locking_no_circular_wait(
    held1: HeldLocks, held2: HeldLocks,
    level_a: nat, level_b: nat,
)
    requires
        lock_order_valid(held1),
        lock_order_valid(held2),
        // Thread 1 holds something at level_a
        exists|obj: nat| held1.locks.contains((obj, level_a)),
        // Thread 1 wants level_b
        can_acquire_at_level(held1, level_b),
    ensures
        // Thread 2 can't simultaneously hold level_b and want level_a
        !circular_wait_levels(level_a, level_b, held1.max_level, held2.max_level),
{
    lemma_ordered_no_circular_wait(level_a, level_b, held1.max_level, held2.max_level);
}

} // verus!
