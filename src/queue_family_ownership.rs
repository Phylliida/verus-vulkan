use vstd::prelude::*;
use crate::resource::*;
use crate::flags::*;
use crate::sync::*;

verus! {

//  ── Queue Family Ownership Transfers ───────────────────────────────────
//
//  In Vulkan, when a resource is used by queues in different queue families,
//  explicit ownership transfer is required. This is a two-step process:
//  1. Release barrier on the source queue (makes writes available)
//  2. Acquire barrier on the destination queue (makes writes visible)
//  Both barriers must specify matching queue family indices and layout.

///  Queue family index.
pub type QueueFamilyIndex = nat;

///  Sentinel value indicating no queue family ownership (shared/concurrent).
pub open spec fn QUEUE_FAMILY_IGNORED() -> nat { 0xFFFF_FFFF }

///  Sharing mode for a resource.
pub enum SharingMode {
    ///  Resource is exclusively owned by one queue family at a time.
    ///  Requires explicit ownership transfers.
    Exclusive,
    ///  Resource can be accessed by multiple queue families concurrently.
    ///  No ownership transfers needed, but may be slower.
    Concurrent,
}

///  Ownership state of a resource.
pub struct OwnershipState {
    ///  The resource being tracked.
    pub resource: ResourceId,
    ///  Current owning queue family (None if concurrent or not yet acquired).
    pub owner: Option<QueueFamilyIndex>,
    ///  Sharing mode.
    pub sharing_mode: SharingMode,
    ///  Whether a release has been issued but not yet matched by an acquire.
    pub pending_release: bool,
    ///  Queue family that issued the pending release (if any).
    pub release_from: Option<QueueFamilyIndex>,
    ///  Queue family that should acquire (if any).
    pub release_to: Option<QueueFamilyIndex>,
}

///  A release barrier for queue family ownership transfer.
pub struct ReleaseBarrier {
    ///  The resource being released.
    pub resource: ResourceId,
    ///  Source queue family (current owner).
    pub src_queue_family: QueueFamilyIndex,
    ///  Destination queue family (new owner).
    pub dst_queue_family: QueueFamilyIndex,
    ///  Sync scope of the release.
    pub src_stages: PipelineStageFlags,
    pub src_accesses: AccessFlags,
    pub dst_stages: PipelineStageFlags,
    pub dst_accesses: AccessFlags,
}

///  An acquire barrier for queue family ownership transfer.
pub struct AcquireBarrier {
    ///  The resource being acquired.
    pub resource: ResourceId,
    ///  Source queue family (previous owner, must match release).
    pub src_queue_family: QueueFamilyIndex,
    ///  Destination queue family (new owner, must match release).
    pub dst_queue_family: QueueFamilyIndex,
    ///  Sync scope of the acquire.
    pub src_stages: PipelineStageFlags,
    pub src_accesses: AccessFlags,
    pub dst_stages: PipelineStageFlags,
    pub dst_accesses: AccessFlags,
}

//  ── Spec Functions ──────────────────────────────────────────────────────

///  Create initial ownership state for a resource.
pub open spec fn initial_ownership(
    resource: ResourceId,
    owner: QueueFamilyIndex,
    sharing_mode: SharingMode,
) -> OwnershipState {
    OwnershipState {
        resource,
        owner: match sharing_mode {
            SharingMode::Exclusive => Some(owner),
            SharingMode::Concurrent => None,
        },
        sharing_mode,
        pending_release: false,
        release_from: None,
        release_to: None,
    }
}

///  A resource can be used by a queue if:
///  - It's in concurrent mode (any queue family can use it), or
///  - It's in exclusive mode and owned by this queue family.
pub open spec fn can_use_on_queue(
    state: OwnershipState,
    queue_family: QueueFamilyIndex,
) -> bool {
    match state.sharing_mode {
        SharingMode::Concurrent => true,
        SharingMode::Exclusive => {
            state.owner == Some(queue_family)
            && !state.pending_release
        },
    }
}

///  A release barrier is valid: the resource must be owned by src_queue_family.
pub open spec fn release_valid(
    state: OwnershipState,
    release: ReleaseBarrier,
) -> bool {
    state.resource == release.resource
    && state.sharing_mode is Exclusive
    && state.owner == Some(release.src_queue_family)
    && !state.pending_release
    && release.src_queue_family != release.dst_queue_family
}

///  Apply a release barrier: resource enters pending_release state.
pub open spec fn apply_release(
    state: OwnershipState,
    release: ReleaseBarrier,
) -> OwnershipState
    recommends release_valid(state, release),
{
    OwnershipState {
        pending_release: true,
        release_from: Some(release.src_queue_family),
        release_to: Some(release.dst_queue_family),
        ..state
    }
}

///  An acquire barrier is valid: queue families must match the pending release.
pub open spec fn acquire_valid(
    state: OwnershipState,
    acquire: AcquireBarrier,
) -> bool {
    state.resource == acquire.resource
    && state.sharing_mode is Exclusive
    && state.pending_release
    && state.release_from == Some(acquire.src_queue_family)
    && state.release_to == Some(acquire.dst_queue_family)
}

///  Apply an acquire barrier: resource is now owned by dst_queue_family.
pub open spec fn apply_acquire(
    state: OwnershipState,
    acquire: AcquireBarrier,
) -> OwnershipState
    recommends acquire_valid(state, acquire),
{
    OwnershipState {
        owner: Some(acquire.dst_queue_family),
        pending_release: false,
        release_from: None,
        release_to: None,
        ..state
    }
}

///  A complete ownership transfer (release + acquire) is valid.
pub open spec fn transfer_valid(
    state: OwnershipState,
    release: ReleaseBarrier,
    acquire: AcquireBarrier,
) -> bool {
    release_valid(state, release)
    && release.resource == acquire.resource
    && release.src_queue_family == acquire.src_queue_family
    && release.dst_queue_family == acquire.dst_queue_family
}

///  Apply a complete transfer (release then acquire).
pub open spec fn apply_transfer(
    state: OwnershipState,
    release: ReleaseBarrier,
    acquire: AcquireBarrier,
) -> OwnershipState
    recommends transfer_valid(state, release, acquire),
{
    apply_acquire(apply_release(state, release), acquire)
}

///  A concurrent resource can always be used without transfers.
pub open spec fn no_transfer_needed(state: OwnershipState) -> bool {
    state.sharing_mode is Concurrent
}

//  ── Proofs ──────────────────────────────────────────────────────────────

///  Initial exclusive ownership is usable by the initial owner.
pub proof fn lemma_initial_owner_can_use(
    resource: ResourceId,
    owner: QueueFamilyIndex,
)
    ensures can_use_on_queue(
        initial_ownership(resource, owner, SharingMode::Exclusive),
        owner,
    ),
{
}

///  Initial exclusive ownership is NOT usable by another queue family.
pub proof fn lemma_initial_other_cannot_use(
    resource: ResourceId,
    owner: QueueFamilyIndex,
    other: QueueFamilyIndex,
)
    requires owner != other,
    ensures !can_use_on_queue(
        initial_ownership(resource, owner, SharingMode::Exclusive),
        other,
    ),
{
}

///  Concurrent resources are always usable by any queue family.
pub proof fn lemma_concurrent_always_usable(
    resource: ResourceId,
    owner: QueueFamilyIndex,
    any_family: QueueFamilyIndex,
)
    ensures can_use_on_queue(
        initial_ownership(resource, owner, SharingMode::Concurrent),
        any_family,
    ),
{
}

///  After a valid release, the resource is not usable (pending transfer).
pub proof fn lemma_released_not_usable(
    state: OwnershipState,
    release: ReleaseBarrier,
    queue_family: QueueFamilyIndex,
)
    requires
        release_valid(state, release),
    ensures
        !can_use_on_queue(apply_release(state, release), queue_family),
{
}

///  After a valid transfer, the resource is usable by the new owner.
pub proof fn lemma_transfer_new_owner_can_use(
    state: OwnershipState,
    release: ReleaseBarrier,
    acquire: AcquireBarrier,
)
    requires
        transfer_valid(state, release, acquire),
    ensures
        can_use_on_queue(apply_transfer(state, release, acquire), acquire.dst_queue_family),
{
}

///  After a valid transfer, the old owner can no longer use the resource.
pub proof fn lemma_transfer_old_owner_cannot_use(
    state: OwnershipState,
    release: ReleaseBarrier,
    acquire: AcquireBarrier,
)
    requires
        transfer_valid(state, release, acquire),
        release.src_queue_family != release.dst_queue_family,
    ensures
        !can_use_on_queue(apply_transfer(state, release, acquire), release.src_queue_family),
{
}

///  Transfer preserves the resource identity.
pub proof fn lemma_transfer_preserves_resource(
    state: OwnershipState,
    release: ReleaseBarrier,
    acquire: AcquireBarrier,
)
    requires transfer_valid(state, release, acquire),
    ensures apply_transfer(state, release, acquire).resource == state.resource,
{
}

///  Transfer clears the pending_release state.
pub proof fn lemma_transfer_clears_pending(
    state: OwnershipState,
    release: ReleaseBarrier,
    acquire: AcquireBarrier,
)
    requires transfer_valid(state, release, acquire),
    ensures !apply_transfer(state, release, acquire).pending_release,
{
}

///  An acquire must match the release's queue families.
pub proof fn lemma_acquire_must_match_release(
    state: OwnershipState,
    release: ReleaseBarrier,
    acquire: AcquireBarrier,
)
    requires
        release_valid(state, release),
        acquire_valid(apply_release(state, release), acquire),
    ensures
        acquire.src_queue_family == release.src_queue_family,
        acquire.dst_queue_family == release.dst_queue_family,
{
}

} //  verus!
