use vstd::prelude::*;
use crate::resource::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// Lifecycle state of a GPU resource (buffer or image).
pub enum ResourceLifecycle {
    /// Resource has been created but not yet bound to memory.
    Created,
    /// Resource is bound to memory and ready for use.
    Bound,
    /// Resource is currently in use by the GPU (referenced by pending submissions).
    InUse,
    /// Resource is no longer in use and can be safely destroyed.
    Idle,
    /// Resource has been destroyed.
    Destroyed,
}

/// Ghost state tracking a resource's full lifecycle.
pub struct ResourceLifecycleState {
    pub resource: ResourceId,
    pub lifecycle: ResourceLifecycle,
    /// Number of pending submissions referencing this resource.
    pub pending_use_count: nat,
}

// ── Helpers ─────────────────────────────────────────────────────────────

/// Extract the primary nat id from a ResourceId for sync token lookup.
pub open spec fn resource_sync_id(r: ResourceId) -> nat {
    match r {
        ResourceId::Buffer { id } => id,
        ResourceId::Image { id, .. } => id,
        ResourceId::SwapchainImage { swapchain_id, .. } => swapchain_id,
        ResourceId::DescriptorSet { id } => id,
    }
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// Create a resource (enters Created state).
pub open spec fn create_resource(resource: ResourceId) -> ResourceLifecycleState {
    ResourceLifecycleState {
        resource,
        lifecycle: ResourceLifecycle::Created,
        pending_use_count: 0,
    }
}

/// Bind resource to memory (Created → Bound).
pub open spec fn bind_resource(state: ResourceLifecycleState) -> ResourceLifecycleState {
    ResourceLifecycleState {
        lifecycle: ResourceLifecycle::Bound,
        ..state
    }
}

/// Resource is submitted for GPU use (Bound/Idle → InUse).
pub open spec fn submit_resource(state: ResourceLifecycleState) -> ResourceLifecycleState {
    ResourceLifecycleState {
        lifecycle: ResourceLifecycle::InUse,
        pending_use_count: state.pending_use_count + 1,
        ..state
    }
}

/// A submission referencing this resource completes.
pub open spec fn complete_use(state: ResourceLifecycleState) -> ResourceLifecycleState
    recommends state.pending_use_count > 0,
{
    let new_count = (state.pending_use_count - 1) as nat;
    ResourceLifecycleState {
        lifecycle: if new_count == 0 { ResourceLifecycle::Idle } else { ResourceLifecycle::InUse },
        pending_use_count: new_count,
        ..state
    }
}

/// Destroy resource (Idle → Destroyed).
pub open spec fn destroy_resource(state: ResourceLifecycleState) -> ResourceLifecycleState {
    ResourceLifecycleState {
        lifecycle: ResourceLifecycle::Destroyed,
        pending_use_count: 0,
        ..state
    }
}

/// Resource can be bound (must be in Created state).
pub open spec fn can_bind(state: ResourceLifecycleState) -> bool {
    state.lifecycle == ResourceLifecycle::Created
}

/// Resource can be used (must be Bound or Idle).
pub open spec fn can_use(state: ResourceLifecycleState) -> bool {
    state.lifecycle == ResourceLifecycle::Bound
    || state.lifecycle == ResourceLifecycle::Idle
}

/// Resource can be safely destroyed (must be Idle with no pending uses).
pub open spec fn can_destroy(state: ResourceLifecycleState) -> bool {
    (state.lifecycle == ResourceLifecycle::Bound
     || state.lifecycle == ResourceLifecycle::Idle)
    && state.pending_use_count == 0
}

/// Resource is alive (not destroyed).
pub open spec fn resource_alive(state: ResourceLifecycleState) -> bool {
    state.lifecycle != ResourceLifecycle::Destroyed
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// A fresh resource can be bound.
pub proof fn lemma_fresh_can_bind(resource: ResourceId)
    ensures can_bind(create_resource(resource)),
{
}

/// After binding, resource can be used.
pub proof fn lemma_bound_can_use(state: ResourceLifecycleState)
    requires can_bind(state),
    ensures can_use(bind_resource(state)),
{
}

/// A resource in use cannot be destroyed.
pub proof fn lemma_in_use_cannot_destroy(state: ResourceLifecycleState)
    requires state.lifecycle == ResourceLifecycle::InUse,
    ensures !can_destroy(state),
{
}

/// After all uses complete, resource is idle and can be destroyed.
pub proof fn lemma_last_complete_enables_destroy(state: ResourceLifecycleState)
    requires
        state.lifecycle == ResourceLifecycle::InUse,
        state.pending_use_count == 1,
    ensures
        can_destroy(complete_use(state)),
{
}

/// After destroy, resource is not alive.
pub proof fn lemma_destroy_not_alive(state: ResourceLifecycleState)
    ensures !resource_alive(destroy_resource(state)),
{
}

/// A fresh resource is alive.
pub proof fn lemma_fresh_is_alive(resource: ResourceId)
    ensures resource_alive(create_resource(resource)),
{
}

/// Submitting increases the pending count.
pub proof fn lemma_submit_increases_count(state: ResourceLifecycleState)
    ensures
        submit_resource(state).pending_use_count == state.pending_use_count + 1,
{
}

/// Completing decreases the pending count.
pub proof fn lemma_complete_decreases_count(state: ResourceLifecycleState)
    requires state.pending_use_count > 0,
    ensures
        complete_use(state).pending_use_count == state.pending_use_count - 1,
{
}

// ── Safety Proofs: Use-After-Free & Double-Destroy ──────────────────────

/// A destroyed resource cannot be used.
pub proof fn lemma_destroyed_cannot_use(state: ResourceLifecycleState)
    requires state.lifecycle == ResourceLifecycle::Destroyed,
    ensures !can_use(state),
{
}

/// A destroyed resource cannot be destroyed again.
pub proof fn lemma_destroyed_cannot_destroy(state: ResourceLifecycleState)
    requires state.lifecycle == ResourceLifecycle::Destroyed,
    ensures !can_destroy(state),
{
}

/// A newly created resource cannot be destroyed (must bind first).
pub proof fn lemma_created_cannot_destroy(state: ResourceLifecycleState)
    requires state.lifecycle == ResourceLifecycle::Created,
    ensures !can_destroy(state),
{
}

/// After destroying, the resource is not alive.
pub proof fn lemma_can_destroy_then_not_alive(state: ResourceLifecycleState)
    requires can_destroy(state),
    ensures !resource_alive(destroy_resource(state)),
{
}

/// A resource cannot be simultaneously usable and destroyed.
pub proof fn lemma_use_and_destroy_exclusive(state: ResourceLifecycleState)
    ensures !(can_use(state) && state.lifecycle == ResourceLifecycle::Destroyed),
{
}

/// A resource in use cannot be bound (binding requires Created state).
pub proof fn lemma_in_use_cannot_bind(state: ResourceLifecycleState)
    requires state.lifecycle == ResourceLifecycle::InUse,
    ensures !can_bind(state),
{
}

} // verus!
