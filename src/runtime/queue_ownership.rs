use vstd::prelude::*;
use crate::resource::*;
use crate::queue_ownership::*;
use crate::sync_token::*;

verus! {

/// Runtime wrapper for tracking queue family ownership of GPU resources.
///
/// Wraps the spec-level QueueFamilyOwnership model, tracking per-resource
/// ownership for exclusive vs concurrent sharing mode.
pub struct RuntimeOwnershipTracker {
    /// Ghost model: resource → queue family ownership.
    pub ownerships: Ghost<Map<ResourceId, QueueFamilyOwnership>>,
}

impl View for RuntimeOwnershipTracker {
    type V = Map<ResourceId, QueueFamilyOwnership>;
    open spec fn view(&self) -> Map<ResourceId, QueueFamilyOwnership> { self.ownerships@ }
}

// ── Specs ───────────────────────────────────────────────────────────────

/// Well-formedness of the ownership tracker.
/// Resources with pending transfers must have an owner (exclusive mode).
pub open spec fn ownership_tracker_wf(tracker: &RuntimeOwnershipTracker) -> bool {
    forall|r: ResourceId| tracker@.contains_key(r) && tracker@[r].release_pending
        ==> tracker@[r].owner.is_some()
}

/// Current owner of a resource.
pub open spec fn resource_owner(
    tracker: &RuntimeOwnershipTracker,
    resource: ResourceId,
) -> Option<nat>
    recommends tracker@.contains_key(resource),
{
    tracker@[resource].owner
}

/// Whether a resource is in concurrent mode.
pub open spec fn is_concurrent(
    tracker: &RuntimeOwnershipTracker,
    resource: ResourceId,
) -> bool {
    tracker@.contains_key(resource)
    && tracker@[resource].owner.is_none()
}

/// Whether a queue family can access a resource.
pub open spec fn can_access_resource(
    tracker: &RuntimeOwnershipTracker,
    resource: ResourceId,
    family: nat,
) -> bool {
    tracker@.contains_key(resource)
    && can_access(tracker@[resource], family)
}

/// Whether a transfer is pending for a resource.
pub open spec fn transfer_pending(
    tracker: &RuntimeOwnershipTracker,
    resource: ResourceId,
) -> bool {
    tracker@.contains_key(resource)
    && tracker@[resource].release_pending
}

/// Count of resources with pending transfers.
pub open spec fn pending_transfers_count(
    tracker: &RuntimeOwnershipTracker,
) -> nat {
    tracker@.dom().filter(|r: ResourceId| tracker@[r].release_pending).len()
}

/// All resources are owned (not in concurrent mode).
pub open spec fn all_owned(tracker: &RuntimeOwnershipTracker) -> bool {
    forall|r: ResourceId| tracker@.contains_key(r)
        ==> tracker@[r].owner.is_some()
}

/// All resources are in concurrent mode.
pub open spec fn all_concurrent(tracker: &RuntimeOwnershipTracker) -> bool {
    forall|r: ResourceId| tracker@.contains_key(r)
        ==> tracker@[r].owner.is_none()
}

/// Release and acquire operations are properly paired.
pub open spec fn release_acquire_paired(
    tracker: &RuntimeOwnershipTracker,
    resource: ResourceId,
    dst_family: nat,
) -> bool {
    tracker@.contains_key(resource)
    && transfer_valid(tracker@[resource], dst_family)
}

// ── Exec Functions ──────────────────────────────────────────────────────

/// Exec: create an empty ownership tracker.
pub fn create_ownership_tracker_exec() -> (out: RuntimeOwnershipTracker)
    ensures
        ownership_tracker_wf(&out),
        out@ == Map::<ResourceId, QueueFamilyOwnership>::empty(),
{
    RuntimeOwnershipTracker {
        ownerships: Ghost(Map::empty()),
    }
}

/// Exec: register a resource with initial exclusive ownership.
pub fn register_resource_exec(
    tracker: &mut RuntimeOwnershipTracker,
    resource: Ghost<ResourceId>,
    family: Ghost<nat>,
)
    ensures
        tracker@ == old(tracker)@.insert(resource@, initial_ownership(family@)),
{
    tracker.ownerships = Ghost(
        tracker.ownerships@.insert(resource@, initial_ownership(family@))
    );
}

/// Exec: register a resource with concurrent ownership.
pub fn register_concurrent_exec(
    tracker: &mut RuntimeOwnershipTracker,
    resource: Ghost<ResourceId>,
)
    ensures
        tracker@ == old(tracker)@.insert(resource@, concurrent_ownership()),
{
    tracker.ownerships = Ghost(
        tracker.ownerships@.insert(resource@, concurrent_ownership())
    );
}

/// Exec: issue a release barrier for ownership transfer.
/// Caller must prove exclusive access to the source queue.
pub fn release_ownership_exec(
    tracker: &mut RuntimeOwnershipTracker,
    resource: Ghost<ResourceId>,
    src_family: Ghost<nat>,
    dst_family: Ghost<nat>,
    queue_id: Ghost<nat>,
    thread: Ghost<ThreadId>,
    reg: Ghost<TokenRegistry>,
)
    requires
        old(tracker)@.contains_key(resource@),
        old(tracker)@[resource@].owner == Some(src_family@),
        !old(tracker)@[resource@].release_pending,
        holds_exclusive(reg@, queue_id@, thread@),
    ensures
        tracker@ == old(tracker)@.insert(
            resource@,
            release_ownership(old(tracker)@[resource@], src_family@, dst_family@),
        ),
{
    let ghost old_ownership = tracker.ownerships@[resource@];
    tracker.ownerships = Ghost(
        tracker.ownerships@.insert(
            resource@,
            release_ownership(old_ownership, src_family@, dst_family@),
        )
    );
}

/// Exec: issue an acquire barrier to complete ownership transfer.
/// Caller must prove exclusive access to the destination queue.
pub fn acquire_ownership_exec(
    tracker: &mut RuntimeOwnershipTracker,
    resource: Ghost<ResourceId>,
    dst_family: Ghost<nat>,
    queue_id: Ghost<nat>,
    thread: Ghost<ThreadId>,
    reg: Ghost<TokenRegistry>,
)
    requires
        old(tracker)@.contains_key(resource@),
        transfer_valid(old(tracker)@[resource@], dst_family@),
        holds_exclusive(reg@, queue_id@, thread@),
    ensures
        tracker@ == old(tracker)@.insert(
            resource@,
            acquire_ownership(old(tracker)@[resource@], dst_family@),
        ),
{
    let ghost old_ownership = tracker.ownerships@[resource@];
    tracker.ownerships = Ghost(
        tracker.ownerships@.insert(
            resource@,
            acquire_ownership(old_ownership, dst_family@),
        )
    );
}

/// Exec: set a resource to concurrent mode.
/// Caller must prove no ownership transfer is in progress.
pub fn set_concurrent_exec(
    tracker: &mut RuntimeOwnershipTracker,
    resource: Ghost<ResourceId>,
)
    requires
        old(tracker)@.contains_key(resource@),
        !old(tracker)@[resource@].release_pending,
    ensures
        tracker@ == old(tracker)@.insert(resource@, concurrent_ownership()),
{
    tracker.ownerships = Ghost(
        tracker.ownerships@.insert(resource@, concurrent_ownership())
    );
}

/// Exec: check if a queue family can access a resource.
pub fn check_access_exec(
    tracker: &RuntimeOwnershipTracker,
    resource: Ghost<ResourceId>,
    family: Ghost<nat>,
) -> (result: Ghost<bool>)
    requires tracker@.contains_key(resource@),
    ensures result@ == can_access(tracker@[resource@], family@),
{
    Ghost(can_access(tracker.ownerships@[resource@], family@))
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// Created tracker is well-formed.
pub proof fn lemma_create_tracker_wf()
    ensures ownership_tracker_wf(&RuntimeOwnershipTracker {
        ownerships: Ghost(Map::<ResourceId, QueueFamilyOwnership>::empty()),
    }),
{
}

/// After release, the transfer is pending.
pub proof fn lemma_release_sets_pending(
    tracker: &RuntimeOwnershipTracker,
    resource: ResourceId,
    src_family: nat,
    dst_family: nat,
)
    requires
        tracker@.contains_key(resource),
        tracker@[resource].owner == Some(src_family),
        !tracker@[resource].release_pending,
    ensures ({
        let released = release_ownership(tracker@[resource], src_family, dst_family);
        released.release_pending
        && released.pending_dst_family == dst_family
    }),
{
}

/// After acquire, the transfer is complete.
pub proof fn lemma_acquire_completes_transfer(
    tracker: &RuntimeOwnershipTracker,
    resource: ResourceId,
    dst_family: nat,
)
    requires
        tracker@.contains_key(resource),
        transfer_valid(tracker@[resource], dst_family),
    ensures ({
        let acquired = acquire_ownership(tracker@[resource], dst_family);
        acquired.owner == Some(dst_family)
        && !acquired.release_pending
    }),
{
}

/// Concurrent resources are always accessible.
pub proof fn lemma_concurrent_always_accessible(
    tracker: &RuntimeOwnershipTracker,
    resource: ResourceId,
    family: nat,
)
    requires
        tracker@.contains_key(resource),
        tracker@[resource].owner.is_none(),
    ensures
        can_access(tracker@[resource], family),
{
    lemma_concurrent_any_family(family);
}

/// Exclusive ownership blocks other families.
pub proof fn lemma_exclusive_blocks_other_family(
    tracker: &RuntimeOwnershipTracker,
    resource: ResourceId,
    owner_family: nat,
    other_family: nat,
)
    requires
        tracker@.contains_key(resource),
        tracker@[resource].owner == Some(owner_family),
        !tracker@[resource].release_pending,
        other_family != owner_family,
    ensures
        !can_access(tracker@[resource], other_family),
{
}

/// Release + acquire roundtrip transfers ownership.
pub proof fn lemma_release_acquire_roundtrip(
    tracker: &RuntimeOwnershipTracker,
    resource: ResourceId,
    src_family: nat,
    dst_family: nat,
)
    requires
        tracker@.contains_key(resource),
        tracker@[resource].owner == Some(src_family),
        !tracker@[resource].release_pending,
    ensures ({
        let released = release_ownership(tracker@[resource], src_family, dst_family);
        let acquired = acquire_ownership(released, dst_family);
        acquired.owner == Some(dst_family)
        && !acquired.release_pending
        && can_access(acquired, dst_family)
    }),
{
    lemma_release_acquire_transfers(tracker@[resource], src_family, dst_family);
}

/// Initial ownership grants access to the creating family.
pub proof fn lemma_initial_ownership_accessible(family: nat)
    ensures can_access(initial_ownership(family), family),
{
    lemma_initial_owner_can_access(family);
}

/// Pending transfer blocks access from both families.
pub proof fn lemma_pending_not_accessible(
    tracker: &RuntimeOwnershipTracker,
    resource: ResourceId,
    src_family: nat,
    dst_family: nat,
)
    requires
        tracker@.contains_key(resource),
        tracker@[resource].owner == Some(src_family),
        !tracker@[resource].release_pending,
        src_family != dst_family,
    ensures ({
        let released = release_ownership(tracker@[resource], src_family, dst_family);
        !can_access(released, src_family) && !can_access(released, dst_family)
    }),
{
    lemma_release_blocks_access(tracker@[resource], src_family, dst_family);
}

/// Releasing one resource preserves other resources' ownership.
pub proof fn lemma_transfer_preserves_other_resources(
    tracker: &RuntimeOwnershipTracker,
    resource: ResourceId,
    other: ResourceId,
    src_family: nat,
    dst_family: nat,
)
    requires
        resource != other,
        tracker@.contains_key(resource),
        tracker@.contains_key(other),
    ensures
        tracker@.insert(
            resource,
            release_ownership(tracker@[resource], src_family, dst_family),
        ).contains_key(other),
        tracker@.insert(
            resource,
            release_ownership(tracker@[resource], src_family, dst_family),
        )[other] == tracker@[other],
{
}

/// Concurrent to exclusive requires an explicit barrier.
pub proof fn lemma_concurrent_to_exclusive_requires_barrier(
    tracker: &RuntimeOwnershipTracker,
    resource: ResourceId,
    family: nat,
)
    requires
        tracker@.contains_key(resource),
        tracker@[resource].owner.is_none(),
    ensures ({
        // Concurrent resource is accessible by any family
        can_access(tracker@[resource], family)
        // But initial_ownership would restrict to one family
        && !can_access(initial_ownership(family), family + 1)
    }),
{
}

} // verus!
