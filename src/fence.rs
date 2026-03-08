use vstd::prelude::*;
use crate::lifetime::*;

verus! {

/// Ghost state for a Vulkan fence.
///
/// Fences provide host-side completion detection: the GPU signals a fence
/// when a submitted batch finishes, and the host can wait on or query it.
pub struct FenceState {
    /// Unique fence identifier.
    pub id: nat,
    /// Whether the fence is currently signaled.
    pub signaled: bool,
    /// The submission that will signal (or has signaled) this fence.
    pub submission_id: Option<nat>,
    /// Whether the fence has not been destroyed.
    pub alive: bool,
}

/// A fence is well-formed if it is alive.
pub open spec fn fence_well_formed(fence: FenceState) -> bool {
    fence.alive
}

/// Create a fresh fence with the given initial signal state.
pub open spec fn create_fence_ghost(id: nat, signaled: bool) -> FenceState {
    FenceState {
        id,
        signaled,
        submission_id: None,
        alive: true,
    }
}

/// Ghost update: mark the fence as signaled by a given submission.
pub open spec fn signal_fence_ghost(fence: FenceState, sub_id: nat) -> FenceState {
    FenceState {
        signaled: true,
        submission_id: Some(sub_id),
        ..fence
    }
}

/// Ghost update: reset the fence to unsignaled.
pub open spec fn reset_fence_ghost(fence: FenceState) -> FenceState {
    FenceState {
        signaled: false,
        submission_id: None,
        ..fence
    }
}

/// Ghost update: destroy the fence.
pub open spec fn destroy_fence_ghost(fence: FenceState) -> FenceState {
    FenceState {
        alive: false,
        ..fence
    }
}

/// No pending (uncompleted) submission references this fence.
pub open spec fn fence_not_pending(
    fence_id: nat,
    pending_submissions: Seq<SubmissionRecord>,
) -> bool {
    forall|i: int| 0 <= i < pending_submissions.len()
        ==> !(#[trigger] pending_submissions[i].fence_id == Some(fence_id)
              && !pending_submissions[i].completed)
}

// ── Lemmas ──────────────────────────────────────────────────────────────

/// A freshly created fence is well-formed.
pub proof fn lemma_create_fence_well_formed(id: nat, signaled: bool)
    ensures fence_well_formed(create_fence_ghost(id, signaled)),
{
}

/// After signaling, the fence is signaled.
pub proof fn lemma_signal_makes_signaled(fence: FenceState, sub_id: nat)
    ensures signal_fence_ghost(fence, sub_id).signaled,
{
}

/// Resetting then signaling yields a signaled fence.
pub proof fn lemma_reset_then_signal_cycle(fence: FenceState, sub_id: nat)
    ensures signal_fence_ghost(reset_fence_ghost(fence), sub_id).signaled,
{
}

/// After reset, the fence is not signaled.
pub proof fn lemma_reset_makes_unsignaled(fence: FenceState)
    ensures !reset_fence_ghost(fence).signaled,
{
}

/// After destroying, the fence is not well-formed.
pub proof fn lemma_destroy_not_well_formed(fence: FenceState)
    ensures !fence_well_formed(destroy_fence_ghost(fence)),
{
}

/// Signaling preserves alive status.
pub proof fn lemma_signal_preserves_alive(fence: FenceState, sub_id: nat)
    requires fence.alive,
    ensures signal_fence_ghost(fence, sub_id).alive,
{
}

/// Reset preserves alive status.
pub proof fn lemma_reset_preserves_alive(fence: FenceState)
    requires fence.alive,
    ensures reset_fence_ghost(fence).alive,
{
}

/// A freshly created fence with signaled=false is not signaled.
pub proof fn lemma_create_unsignaled(id: nat)
    ensures !create_fence_ghost(id, false).signaled,
{
}

} // verus!
