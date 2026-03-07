use vstd::prelude::*;

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

} // verus!
