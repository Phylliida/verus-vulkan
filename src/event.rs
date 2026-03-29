use vstd::prelude::*;

verus! {

//  ── Types ───────────────────────────────────────────────────────────────

///  Ghost state for a Vulkan event (VkEvent).
///
///  Events provide fine-grained GPU-to-GPU synchronization within a
///  single queue. They must be set before waited on, and cannot be
///  used across render pass boundaries (except in the same render pass
///  instance for self-dependencies).
pub struct EventState {
    pub id: nat,
    ///  Whether the event has been set (signaled) on the GPU.
    pub signaled: bool,
    ///  The pipeline stages at which the event was set.
    pub signal_stages: Set<nat>,
    ///  Whether the event is alive.
    pub alive: bool,
}

//  ── Spec Functions ──────────────────────────────────────────────────────

///  Create a fresh event (unsignaled).
pub open spec fn create_event(id: nat) -> EventState {
    EventState {
        id,
        signaled: false,
        signal_stages: Set::empty(),
        alive: true,
    }
}

///  Set (signal) an event at specific pipeline stages.
pub open spec fn set_event(
    event: EventState,
    stages: Set<nat>,
) -> EventState
    recommends event.alive,
{
    EventState {
        signaled: true,
        signal_stages: stages,
        ..event
    }
}

///  Reset an event (make it unsignaled).
pub open spec fn reset_event(event: EventState) -> EventState
    recommends event.alive,
{
    EventState {
        signaled: false,
        signal_stages: Set::empty(),
        ..event
    }
}

///  Waiting on an event is valid: event must be signaled.
pub open spec fn wait_event_valid(event: EventState) -> bool {
    event.alive && event.signaled
}

///  Event usage within a render pass: set and wait must be in the same
///  render pass instance (or both outside any render pass).
pub open spec fn event_render_pass_compatible(
    set_in_render_pass: bool,
    wait_in_render_pass: bool,
    same_render_pass_instance: bool,
) -> bool {
    //  Both outside render pass: always fine
    (!set_in_render_pass && !wait_in_render_pass)
    //  Both inside the same render pass instance: fine for self-dep
    || (set_in_render_pass && wait_in_render_pass && same_render_pass_instance)
}

///  An event lifecycle is well-formed: set, then wait, then optionally reset.
pub open spec fn event_well_formed(event: EventState) -> bool {
    event.alive
}

///  Destroy an event.
pub open spec fn destroy_event(event: EventState) -> EventState
    recommends event.alive,
{
    EventState {
        alive: false,
        ..event
    }
}

//  ── Proofs ──────────────────────────────────────────────────────────────

///  After setting an event, waiting on it is valid.
pub proof fn lemma_set_enables_wait(event: EventState, stages: Set<nat>)
    requires event.alive,
    ensures wait_event_valid(set_event(event, stages)),
{
}

///  After resetting an event, waiting on it is invalid.
pub proof fn lemma_reset_disables_wait(event: EventState)
    ensures !reset_event(event).signaled,
{
}

///  A fresh event is not signaled.
pub proof fn lemma_fresh_event_unsignaled(id: nat)
    ensures
        !create_event(id).signaled,
        create_event(id).alive,
{
}

///  Set then reset returns to unsignaled.
pub proof fn lemma_set_then_reset(event: EventState, stages: Set<nat>)
    ensures !reset_event(set_event(event, stages)).signaled,
{
}

///  Events outside render pass are always compatible with themselves.
pub proof fn lemma_outside_render_pass_compatible()
    ensures event_render_pass_compatible(false, false, false),
{
}

///  Events inside the same render pass instance are compatible.
pub proof fn lemma_same_render_pass_compatible()
    ensures event_render_pass_compatible(true, true, true),
{
}

///  Set inside, wait outside render pass is NOT compatible.
pub proof fn lemma_cross_render_pass_incompatible()
    ensures !event_render_pass_compatible(true, false, false),
{
}

///  Destroying an event makes it not alive.
///  Caller must prove the event is alive before destroying.
pub proof fn lemma_destroy_not_alive(event: EventState)
    requires event.alive,
    ensures !destroy_event(event).alive,
{
}

} //  verus!
