use vstd::prelude::*;
use crate::resource::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// Ownership state of a resource with respect to queue families.
///
/// In Vulkan, resources accessed by multiple queue families require
/// explicit ownership transfers via release/acquire barrier pairs.
/// Without these, GPU caches may not be flushed/invalidated correctly.
pub struct QueueFamilyOwnership {
    /// Current owning queue family (None = unowned / concurrent mode).
    pub owner: Option<nat>,
    /// Whether a release barrier has been issued but acquire not yet done.
    pub release_pending: bool,
    /// Source family of pending transfer (valid when release_pending).
    pub pending_src_family: nat,
    /// Destination family of pending transfer (valid when release_pending).
    pub pending_dst_family: nat,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// Initial ownership: created on a specific queue family.
pub open spec fn initial_ownership(family: nat) -> QueueFamilyOwnership {
    QueueFamilyOwnership {
        owner: Some(family),
        release_pending: false,
        pending_src_family: 0,
        pending_dst_family: 0,
    }
}

/// Concurrent ownership: no specific owner (VK_SHARING_MODE_CONCURRENT).
pub open spec fn concurrent_ownership() -> QueueFamilyOwnership {
    QueueFamilyOwnership {
        owner: None,
        release_pending: false,
        pending_src_family: 0,
        pending_dst_family: 0,
    }
}

/// Whether a resource is owned by the given queue family and can be accessed.
pub open spec fn can_access(ownership: QueueFamilyOwnership, family: nat) -> bool {
    // Concurrent mode: any family can access
    ownership.owner.is_none()
    // Exclusive mode: must be the owner and no pending transfer
    || (ownership.owner == Some(family) && !ownership.release_pending)
}

/// Issue a release barrier: starts an ownership transfer.
pub open spec fn release_ownership(
    ownership: QueueFamilyOwnership,
    src_family: nat,
    dst_family: nat,
) -> QueueFamilyOwnership
    recommends
        ownership.owner == Some(src_family),
        !ownership.release_pending,
{
    QueueFamilyOwnership {
        owner: ownership.owner,
        release_pending: true,
        pending_src_family: src_family,
        pending_dst_family: dst_family,
    }
}

/// Issue an acquire barrier: completes an ownership transfer.
pub open spec fn acquire_ownership(
    ownership: QueueFamilyOwnership,
    dst_family: nat,
) -> QueueFamilyOwnership
    recommends transfer_valid(ownership, dst_family),
{
    QueueFamilyOwnership {
        owner: Some(dst_family),
        release_pending: false,
        pending_src_family: ownership.pending_src_family,
        pending_dst_family: ownership.pending_dst_family,
    }
}

/// An ownership transfer is valid: release must have been issued with
/// matching destination, and the source must have been the owner.
pub open spec fn transfer_valid(
    ownership: QueueFamilyOwnership,
    dst_family: nat,
) -> bool {
    ownership.release_pending
    && ownership.pending_dst_family == dst_family
    && ownership.owner == Some(ownership.pending_src_family)
}

/// Same-family access: no transfer needed.
pub open spec fn same_family_access(
    ownership: QueueFamilyOwnership,
    family: nat,
) -> bool {
    ownership.owner == Some(family) && !ownership.release_pending
}

/// Cross-family access is safe only after a completed transfer.
pub open spec fn cross_family_access_safe(
    before: QueueFamilyOwnership,
    after: QueueFamilyOwnership,
    new_family: nat,
) -> bool {
    can_access(after, new_family)
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// After release + acquire, the new family owns the resource.
pub proof fn lemma_release_acquire_transfers(
    ownership: QueueFamilyOwnership,
    src_family: nat,
    dst_family: nat,
)
    requires
        ownership.owner == Some(src_family),
        !ownership.release_pending,
    ensures ({
        let released = release_ownership(ownership, src_family, dst_family);
        let acquired = acquire_ownership(released, dst_family);
        acquired.owner == Some(dst_family)
        && !acquired.release_pending
        && can_access(acquired, dst_family)
    }),
{
}

/// Same-family access doesn't need a transfer.
pub proof fn lemma_same_family_no_transfer(
    ownership: QueueFamilyOwnership,
    family: nat,
)
    requires
        ownership.owner == Some(family),
        !ownership.release_pending,
    ensures
        can_access(ownership, family),
{
}

/// Concurrent mode allows any family to access.
pub proof fn lemma_concurrent_any_family(family: nat)
    ensures
        can_access(concurrent_ownership(), family),
{
}

/// After release without acquire, no one can access (exclusive mode).
pub proof fn lemma_release_blocks_access(
    ownership: QueueFamilyOwnership,
    src_family: nat,
    dst_family: nat,
)
    requires
        ownership.owner == Some(src_family),
        !ownership.release_pending,
        src_family != dst_family,
    ensures ({
        let released = release_ownership(ownership, src_family, dst_family);
        // Source can't access (release_pending)
        !can_access(released, src_family)
        // Destination can't access yet (still owned by source)
        && !can_access(released, dst_family)
    }),
{
}

/// Initial ownership allows the creating family to access.
pub proof fn lemma_initial_owner_can_access(family: nat)
    ensures
        can_access(initial_ownership(family), family),
{
}

/// A transfer is valid after release with matching dst_family.
pub proof fn lemma_transfer_valid_after_release(
    ownership: QueueFamilyOwnership,
    src_family: nat,
    dst_family: nat,
)
    requires
        ownership.owner == Some(src_family),
        !ownership.release_pending,
    ensures
        transfer_valid(
            release_ownership(ownership, src_family, dst_family),
            dst_family,
        ),
{
}

} // verus!
