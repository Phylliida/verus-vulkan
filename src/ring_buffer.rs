use vstd::prelude::*;

verus! {

//  ── Types ───────────────────────────────────────────────────────────────

///  Ghost state for a ring buffer of frame resources.
///
///  In triple-buffered rendering, the application maintains N sets of
///  per-frame resources (command buffers, descriptor pools, per-frame
///  uniforms). A ring buffer index advances each frame and wraps modulo N.
///  Getting the modular arithmetic wrong causes a frame to overwrite
///  resources still in use by a previous frame's GPU work.
pub struct RingBufferState {
    ///  Unique identifier for this ring buffer (used for thread-safe sync token lookup).
    pub id: nat,
    ///  Total number of slots (e.g., 3 for triple buffering).
    pub capacity: nat,
    ///  Next slot to write (monotonically increasing, use % capacity for index).
    pub write_head: nat,
    ///  Oldest slot still in flight (monotonically increasing, use % capacity for index).
    pub read_head: nat,
}

//  ── Spec Functions ──────────────────────────────────────────────────────

///  Number of frames currently in flight.
pub open spec fn frames_in_flight(ring: RingBufferState) -> nat
    recommends ring.read_head <= ring.write_head,
{
    (ring.write_head - ring.read_head) as nat
}

///  The actual slot index for the write head.
pub open spec fn write_slot(ring: RingBufferState) -> nat
    recommends ring.capacity > 0,
{
    ring.write_head % ring.capacity
}

///  The actual slot index for the read head.
pub open spec fn read_slot(ring: RingBufferState) -> nat
    recommends ring.capacity > 0,
{
    ring.read_head % ring.capacity
}

///  The ring buffer is well-formed:
///  - capacity > 0
///  - read_head <= write_head
///  - frames_in_flight < capacity (at least one free slot)
pub open spec fn ring_well_formed(ring: RingBufferState) -> bool {
    ring.capacity > 0
    && ring.read_head <= ring.write_head
    && frames_in_flight(ring) < ring.capacity
}

///  The ring buffer is in a valid initial state.
pub open spec fn ring_initial(ring: RingBufferState) -> bool {
    ring.capacity > 0
    && ring.write_head == 0
    && ring.read_head == 0
}

///  Advance the write head (acquire a new frame slot).
pub open spec fn ring_acquire(ring: RingBufferState) -> RingBufferState {
    RingBufferState {
        write_head: ring.write_head + 1,
        ..ring
    }
}

///  Advance the read head (retire an old frame after fence wait).
pub open spec fn ring_retire(ring: RingBufferState) -> RingBufferState {
    RingBufferState {
        read_head: ring.read_head + 1,
        ..ring
    }
}

///  A full frame cycle: retire one old frame, then acquire a new one.
pub open spec fn ring_frame_cycle(ring: RingBufferState) -> RingBufferState {
    ring_acquire(ring_retire(ring))
}

///  Two slot indices are distinct (no aliasing).
pub open spec fn slots_distinct(ring: RingBufferState, a: nat, b: nat) -> bool
    recommends ring.capacity > 0,
{
    a % ring.capacity != b % ring.capacity
}

///  All in-flight slots are pairwise distinct (no resource aliasing).
pub open spec fn no_slot_aliasing(ring: RingBufferState) -> bool {
    forall|i: nat, j: nat|
        #![trigger (ring.read_head + i) % ring.capacity, (ring.read_head + j) % ring.capacity]
        i < frames_in_flight(ring) && j < frames_in_flight(ring) && i != j
        ==> (ring.read_head + i) % ring.capacity != (ring.read_head + j) % ring.capacity
}

//  ── Proofs ──────────────────────────────────────────────────────────────

///  An initial ring buffer is well-formed.
pub proof fn lemma_initial_ring_well_formed(ring: RingBufferState)
    requires ring_initial(ring),
    ensures ring_well_formed(ring),
{
}

///  An initial ring buffer has 0 frames in flight.
pub proof fn lemma_initial_ring_empty(ring: RingBufferState)
    requires ring_initial(ring),
    ensures frames_in_flight(ring) == 0,
{
}

///  Acquiring increases frames_in_flight by 1.
pub proof fn lemma_acquire_increments(ring: RingBufferState)
    requires ring_well_formed(ring),
    ensures
        frames_in_flight(ring_acquire(ring)) == frames_in_flight(ring) + 1,
{
}

///  Acquiring preserves well-formedness if there's room.
pub proof fn lemma_acquire_preserves_well_formed(ring: RingBufferState)
    requires
        ring_well_formed(ring),
        frames_in_flight(ring) + 1 < ring.capacity,
    ensures
        ring_well_formed(ring_acquire(ring)),
{
}

///  Retiring decreases frames_in_flight by 1.
pub proof fn lemma_retire_decrements(ring: RingBufferState)
    requires
        ring_well_formed(ring),
        frames_in_flight(ring) > 0,
    ensures
        frames_in_flight(ring_retire(ring)) == frames_in_flight(ring) - 1,
{
}

///  Retiring preserves well-formedness.
pub proof fn lemma_retire_preserves_well_formed(ring: RingBufferState)
    requires
        ring_well_formed(ring),
        frames_in_flight(ring) > 0,
    ensures
        ring_well_formed(ring_retire(ring)),
{
}

///  A full frame cycle (retire + acquire) preserves frames_in_flight.
pub proof fn lemma_frame_cycle_preserves_in_flight(ring: RingBufferState)
    requires
        ring_well_formed(ring),
        frames_in_flight(ring) > 0,
    ensures
        frames_in_flight(ring_frame_cycle(ring)) == frames_in_flight(ring),
{
    let retired = ring_retire(ring);
    assert(frames_in_flight(retired) == frames_in_flight(ring) - 1);
    let acquired = ring_acquire(retired);
    assert(frames_in_flight(acquired) == frames_in_flight(retired) + 1);
}

///  A full frame cycle preserves well-formedness.
pub proof fn lemma_frame_cycle_preserves_well_formed(ring: RingBufferState)
    requires
        ring_well_formed(ring),
        frames_in_flight(ring) > 0,
    ensures
        ring_well_formed(ring_frame_cycle(ring)),
{
    lemma_retire_preserves_well_formed(ring);
    let retired = ring_retire(ring);
    assert(frames_in_flight(retired) == frames_in_flight(ring) - 1);
    assert(frames_in_flight(retired) + 1 < ring.capacity);
    lemma_acquire_preserves_well_formed(retired);
}

///  The write slot and read slot are distinct when frames are in flight
///  and frames_in_flight < capacity.
pub proof fn lemma_write_read_slots_distinct(ring: RingBufferState)
    requires
        ring_well_formed(ring),
        frames_in_flight(ring) > 0,
    ensures
        write_slot(ring) != read_slot(ring),
{
    //  write_head = read_head + frames_in_flight
    //  0 < frames_in_flight < capacity
    //  So write_head % capacity != read_head % capacity
    //  because the difference (frames_in_flight) is in (0, capacity)
    let diff = frames_in_flight(ring);
    assert(ring.write_head == ring.read_head + diff);
    assert(0 < diff && diff < ring.capacity);
    //  write_head % cap = (read_head + diff) % cap
    //  If this equaled read_head % cap, then diff % cap == 0, meaning diff is a multiple of cap.
    //  But 0 < diff < cap means diff can't be a multiple of cap.
    assert(write_slot(ring) != read_slot(ring)) by(nonlinear_arith)
        requires
            ring.write_head == ring.read_head + diff,
            0 < diff,
            diff < ring.capacity,
            ring.capacity > 0;
}

///  After retire, the old read slot is now free (not equal to new read slot),
///  provided there's more than one frame in flight.
pub proof fn lemma_retire_frees_slot(ring: RingBufferState)
    requires
        ring_well_formed(ring),
        frames_in_flight(ring) > 1,
    ensures
        read_slot(ring) != read_slot(ring_retire(ring)),
{
    let retired = ring_retire(ring);
    assert(retired.read_head == ring.read_head + 1);
    assert(retired.capacity == ring.capacity);
    //  read_slot(ring) = ring.read_head % cap
    //  read_slot(retired) = (ring.read_head + 1) % cap
    //  These differ because 1 < cap (since frames_in_flight > 1 and cap > frames_in_flight)
    assert(ring.capacity > 1);
    //  (a+1) % c != a % c when c > 1:
    //  If they were equal, then ((a+1) - a) % c == 0, i.e. 1 % c == 0.
    //  But 1 % c == 1 when c > 1. Contradiction.
    let a = ring.read_head;
    let c = ring.capacity;
    assert((a + 1) % c != a % c) by(nonlinear_arith)
        requires c > 1, a >= 0;
    assert(read_slot(retired) == (a + 1) % c);
    assert(read_slot(ring) == a % c);
}

///  No slot aliasing holds when frames_in_flight < capacity.
///  (The pigeonhole principle: distinct offsets mod capacity are distinct.)
pub proof fn lemma_no_aliasing_when_well_formed(ring: RingBufferState)
    requires
        ring_well_formed(ring),
    ensures
        no_slot_aliasing(ring),
{
    assert forall|i: nat, j: nat|
        #![trigger (ring.read_head + i) % ring.capacity, (ring.read_head + j) % ring.capacity]
        i < frames_in_flight(ring) && j < frames_in_flight(ring) && i != j
        implies (ring.read_head + i) % ring.capacity != (ring.read_head + j) % ring.capacity by {
        //  WLOG assume i < j. Then 0 < j - i < capacity.
        //  If (read + i) % cap == (read + j) % cap, then (j - i) % cap == 0,
        //  but 0 < j - i < cap, contradiction.
        if i < j {
            assert((ring.read_head + i) % ring.capacity
                != (ring.read_head + j) % ring.capacity) by(nonlinear_arith)
                requires
                    i < j,
                    j < ring.capacity,
                    ring.capacity > 0;
        } else {
            //  j < i case
            assert((ring.read_head + i) % ring.capacity
                != (ring.read_head + j) % ring.capacity) by(nonlinear_arith)
                requires
                    j < i,
                    i < ring.capacity,
                    ring.capacity > 0;
        }
    }
}

///  Starting from an initial state and doing N frame cycles preserves well-formedness,
///  as long as we stay within capacity.
pub proof fn lemma_n_cycles_well_formed(
    ring: RingBufferState,
    warmup: nat,
)
    requires
        ring_initial(ring),
        warmup < ring.capacity,
    ensures ({
        //  After warmup acquires (filling the pipeline), ring is well-formed
        let filled = n_acquires(ring, warmup);
        ring_well_formed(filled)
        && frames_in_flight(filled) == warmup
    }),
    decreases warmup,
{
    if warmup == 0 {
    } else {
        lemma_n_cycles_well_formed(ring, (warmup - 1) as nat);
        let prev = n_acquires(ring, (warmup - 1) as nat);
        lemma_n_acquires_write_head(ring, (warmup - 1) as nat);
        //  n_acquires preserves capacity and read_head
        assert(prev.capacity == ring.capacity);
        assert(prev.read_head == ring.read_head);
        assert(ring_well_formed(prev));
        assert(frames_in_flight(prev) == warmup - 1);
        assert(frames_in_flight(prev) + 1 < ring.capacity);
        lemma_acquire_preserves_well_formed(prev);
    }
}

///  N acquires on a ring buffer.
pub open spec fn n_acquires(ring: RingBufferState, count: nat) -> RingBufferState
    decreases count,
{
    if count == 0 {
        ring
    } else {
        ring_acquire(n_acquires(ring, (count - 1) as nat))
    }
}

///  N acquires simply advance write_head by count.
pub proof fn lemma_n_acquires_write_head(ring: RingBufferState, count: nat)
    ensures
        n_acquires(ring, count).write_head == ring.write_head + count,
        n_acquires(ring, count).read_head == ring.read_head,
        n_acquires(ring, count).capacity == ring.capacity,
    decreases count,
{
    if count > 0 {
        lemma_n_acquires_write_head(ring, (count - 1) as nat);
    }
}

} //  verus!
