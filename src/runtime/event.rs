use vstd::prelude::*;
use crate::event::*;
use crate::lifetime::*;
use crate::sync_token::*;
use super::device::RuntimeDevice;

verus! {

/// Runtime wrapper for a Vulkan event (VkEvent).
pub struct RuntimeEvent {
    /// Opaque handle (maps to VkEvent).
    pub handle: u64,
    /// Ghost model of the event state.
    pub state: Ghost<EventState>,
}

impl View for RuntimeEvent {
    type V = EventState;
    open spec fn view(&self) -> EventState { self.state@ }
}

/// Well-formedness of the runtime event.
pub open spec fn runtime_event_wf(event: &RuntimeEvent) -> bool {
    event_well_formed(event@)
}

/// Exec: create an event.
pub fn create_event_exec(id: Ghost<nat>) -> (out: RuntimeEvent)
    ensures
        out@ == create_event(id@),
        runtime_event_wf(&out),
{
    RuntimeEvent {
        handle: 0,
        state: Ghost(create_event(id@)),
    }
}

/// Exec: destroy an event.
pub fn destroy_event_exec(
    event: &mut RuntimeEvent,
    dev: &RuntimeDevice,
    thread: Ghost<ThreadId>,
    reg: Ghost<TokenRegistry>,
)
    requires
        runtime_event_wf(&*old(event)),
        forall|i: int| 0 <= i < dev@.pending_submissions.len()
            ==> (#[trigger] dev@.pending_submissions[i]).completed,
        holds_exclusive(reg@, SyncObjectId::Handle(old(event)@.id), thread@),
    ensures
        event@ == destroy_event(old(event)@),
        !event@.alive,
{
    event.state = Ghost(destroy_event(event.state@));
}

/// Exec: set (signal) an event at specific pipeline stages.
pub fn set_event_exec(
    event: &mut RuntimeEvent,
    stages: Ghost<Set<nat>>,
)
    requires
        runtime_event_wf(&*old(event)),
    ensures
        event@ == set_event(old(event)@, stages@),
        runtime_event_wf(event),
{
    event.state = Ghost(set_event(event.state@, stages@));
}

/// Exec: reset an event.
pub fn reset_event_exec(event: &mut RuntimeEvent)
    requires
        runtime_event_wf(&*old(event)),
    ensures
        event@ == reset_event(old(event)@),
        runtime_event_wf(event),
{
    event.state = Ghost(reset_event(event.state@));
}

// ── Specs & Proofs ──────────────────────────────────────────────────

/// Event is alive.
pub open spec fn event_alive(event: &RuntimeEvent) -> bool {
    event@.alive
}

/// Event is signaled.
pub open spec fn event_signaled(event: &RuntimeEvent) -> bool {
    event@.signaled
}

/// Proof: creating an event produces an alive, unsignaled event.
pub proof fn lemma_create_event_alive(id: Ghost<nat>)
    ensures
        event_alive(&RuntimeEvent {
            handle: 0,
            state: Ghost(create_event(id@)),
        }),
        !event_signaled(&RuntimeEvent {
            handle: 0,
            state: Ghost(create_event(id@)),
        }),
{
}

/// Proof: destroying an event preserves its id.
pub proof fn lemma_destroy_event_preserves_id(event: &RuntimeEvent)
    requires runtime_event_wf(event),
    ensures destroy_event(event@).id == event@.id,
{
}

} // verus!
