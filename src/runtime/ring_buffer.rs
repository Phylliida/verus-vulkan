use vstd::prelude::*;
use crate::ring_buffer::*;

verus! {

///  Runtime wrapper for ring buffer frame resource management.
pub struct RuntimeRingBuffer {
    ///  Ghost model of the ring buffer state.
    pub state: Ghost<RingBufferState>,
}

impl View for RuntimeRingBuffer {
    type V = RingBufferState;
    open spec fn view(&self) -> RingBufferState { self.state@ }
}

///  Well-formedness of the runtime ring buffer.
pub open spec fn runtime_ring_wf(ring: &RuntimeRingBuffer) -> bool {
    ring_well_formed(ring@)
}

///  Exec: create a ring buffer from initial ghost state.
pub fn create_ring_buffer_exec(
    ring_state: Ghost<RingBufferState>,
) -> (out: RuntimeRingBuffer)
    requires ring_initial(ring_state@),
    ensures
        out@ == ring_state@,
        runtime_ring_wf(&out),
{
    proof { lemma_initial_ring_well_formed(ring_state@); }
    RuntimeRingBuffer { state: ring_state }
}

///  Exec: acquire a new frame slot (advance write head).
pub fn ring_acquire_exec(ring: &mut RuntimeRingBuffer)
    requires
        runtime_ring_wf(&*old(ring)),
        frames_in_flight(old(ring)@) + 1 < old(ring)@.capacity,
    ensures
        ring@ == ring_acquire(old(ring)@),
        runtime_ring_wf(ring),
{
    proof { lemma_acquire_preserves_well_formed(ring.state@); }
    ring.state = Ghost(ring_acquire(ring.state@));
}

///  Exec: retire an old frame (advance read head after fence wait).
pub fn ring_retire_exec(ring: &mut RuntimeRingBuffer)
    requires
        runtime_ring_wf(&*old(ring)),
        frames_in_flight(old(ring)@) > 0,
    ensures
        ring@ == ring_retire(old(ring)@),
        runtime_ring_wf(ring),
{
    proof { lemma_retire_preserves_well_formed(ring.state@); }
    ring.state = Ghost(ring_retire(ring.state@));
}

///  Exec: full frame cycle (retire + acquire).
pub fn ring_frame_cycle_exec(ring: &mut RuntimeRingBuffer)
    requires
        runtime_ring_wf(&*old(ring)),
        frames_in_flight(old(ring)@) > 0,
    ensures
        ring@ == ring_frame_cycle(old(ring)@),
        runtime_ring_wf(ring),
{
    proof { lemma_frame_cycle_preserves_well_formed(ring.state@); }
    ring.state = Ghost(ring_frame_cycle(ring.state@));
}

} //  verus!
