use vstd::prelude::*;
use crate::resource::*;
use crate::resource_lifecycle::*;

verus! {

/// Runtime wrapper for a GPU resource lifecycle tracker.
pub struct RuntimeResourceLifecycle {
    /// Opaque handle for the resource.
    pub handle: u64,
    /// Ghost model of the resource lifecycle state.
    pub state: Ghost<ResourceLifecycleState>,
}

impl View for RuntimeResourceLifecycle {
    type V = ResourceLifecycleState;
    open spec fn view(&self) -> ResourceLifecycleState { self.state@ }
}

/// Well-formedness: resource is alive.
pub open spec fn runtime_resource_lifecycle_wf(
    rl: &RuntimeResourceLifecycle,
) -> bool {
    resource_alive(rl@)
}

/// Exec: create a resource lifecycle tracker (enters Created state).
pub fn create_resource_lifecycle_exec(
    resource: Ghost<ResourceId>,
) -> (out: RuntimeResourceLifecycle)
    ensures
        out@ == create_resource(resource@),
        runtime_resource_lifecycle_wf(&out),
        can_bind(out@),
{
    proof {
        lemma_fresh_can_bind(resource@);
        lemma_fresh_is_alive(resource@);
    }
    RuntimeResourceLifecycle {
        handle: 0,
        state: Ghost(create_resource(resource@)),
    }
}

/// Exec: bind resource to memory (Created → Bound).
pub fn bind_resource_exec(
    rl: &mut RuntimeResourceLifecycle,
)
    requires
        runtime_resource_lifecycle_wf(&*old(rl)),
        can_bind(old(rl)@),
    ensures
        rl@ == bind_resource(old(rl)@),
        can_use(rl@),
        rl@.resource == old(rl)@.resource,
{
    proof { lemma_bound_can_use(rl.state@); }
    rl.state = Ghost(bind_resource(rl.state@));
}

/// Exec: submit resource for GPU use (Bound/Idle → InUse).
pub fn submit_resource_exec(
    rl: &mut RuntimeResourceLifecycle,
)
    requires
        runtime_resource_lifecycle_wf(&*old(rl)),
        can_use(old(rl)@),
    ensures
        rl@ == submit_resource(old(rl)@),
        rl@.pending_use_count == old(rl)@.pending_use_count + 1,
        rl@.resource == old(rl)@.resource,
{
    rl.state = Ghost(submit_resource(rl.state@));
}

/// Exec: a submission referencing this resource completes.
pub fn complete_use_exec(
    rl: &mut RuntimeResourceLifecycle,
)
    requires
        runtime_resource_lifecycle_wf(&*old(rl)),
        old(rl)@.pending_use_count > 0,
    ensures
        rl@ == complete_use(old(rl)@),
        rl@.pending_use_count == old(rl)@.pending_use_count - 1,
        rl@.resource == old(rl)@.resource,
{
    rl.state = Ghost(complete_use(rl.state@));
}

/// Exec: destroy resource (Bound/Idle + pending==0 → Destroyed).
pub fn destroy_resource_exec(
    rl: &mut RuntimeResourceLifecycle,
)
    requires
        runtime_resource_lifecycle_wf(&*old(rl)),
        can_destroy(old(rl)@),
    ensures
        rl@ == destroy_resource(old(rl)@),
        !resource_alive(rl@),
{
    proof { lemma_destroy_not_alive(rl.state@); }
    rl.state = Ghost(destroy_resource(rl.state@));
}

// ── Proofs ──────────────────────────────────────────────────────────

/// Full happy-path lifecycle traversal: create → bind → submit → complete → destroy.
pub proof fn lemma_lifecycle_create_to_destroy(resource: ResourceId)
    ensures ({
        let s0 = create_resource(resource);
        let s1 = bind_resource(s0);
        let s2 = submit_resource(s1);
        let s3 = complete_use(s2);
        can_destroy(s3)
        && !resource_alive(destroy_resource(s3))
    }),
{
    let s0 = create_resource(resource);
    lemma_fresh_can_bind(resource);
    lemma_bound_can_use(s0);
    let s1 = bind_resource(s0);
    let s2 = submit_resource(s1);
    lemma_last_complete_enables_destroy(s2);
}

/// After destroy, no operations are possible.
pub proof fn lemma_use_after_destroy_impossible(state: ResourceLifecycleState)
    requires !resource_alive(state),
    ensures
        !can_use(state),
        !can_bind(state),
        !can_destroy(state),
{
    lemma_destroyed_cannot_use(state);
    lemma_destroyed_cannot_destroy(state);
}

/// Submitting preserves alive status.
pub proof fn lemma_submit_preserves_alive(state: ResourceLifecycleState)
    requires
        resource_alive(state),
        can_use(state),
    ensures
        resource_alive(submit_resource(state)),
{
}

} // verus!
