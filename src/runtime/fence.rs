use vstd::prelude::*;
use crate::fence::*;
use crate::lifetime::*;
use crate::sync_token::*;

verus! {

/// Runtime wrapper for a Vulkan fence.
pub struct RuntimeFence {
    /// Opaque handle (maps to VkFence).
    pub handle: u64,
    /// Ghost model of the fence state.
    pub state: Ghost<FenceState>,
}

impl View for RuntimeFence {
    type V = FenceState;
    open spec fn view(&self) -> FenceState { self.state@ }
}

/// Well-formedness of the runtime fence.
pub open spec fn runtime_fence_wf(fence: &RuntimeFence) -> bool {
    fence_well_formed(fence@)
}

/// Exec: create a fence.
pub fn create_fence_exec(id: Ghost<nat>, signaled: bool) -> (out: RuntimeFence)
    ensures
        out@ == create_fence_ghost(id@, signaled),
        runtime_fence_wf(&out),
{
    RuntimeFence {
        handle: 0,
        state: Ghost(create_fence_ghost(id@, signaled)),
    }
}

/// Exec: reset a fence to unsignaled.
/// Caller must prove exclusive access to the fence.
pub fn reset_fence_exec(
    fence: &mut RuntimeFence,
    thread: Ghost<ThreadId>,
    reg: Ghost<TokenRegistry>,
)
    requires
        runtime_fence_wf(&*old(fence)),
        holds_exclusive(reg@, old(fence).handle as nat, thread@),
    ensures
        fence@ == reset_fence_ghost(old(fence)@),
{
    fence.state = Ghost(reset_fence_ghost(fence.state@));
}

/// Exec: wait for a fence (marks as signaled in ghost state).
/// Caller must prove exclusive access to the fence.
pub fn wait_fence_exec(
    fence: &mut RuntimeFence,
    sub_id: Ghost<nat>,
    thread: Ghost<ThreadId>,
    reg: Ghost<TokenRegistry>,
)
    requires
        runtime_fence_wf(&*old(fence)),
        holds_exclusive(reg@, old(fence).handle as nat, thread@),
    ensures
        fence@ == signal_fence_ghost(old(fence)@, sub_id@),
        fence@.signaled,
{
    fence.state = Ghost(signal_fence_ghost(fence.state@, sub_id@));
}

/// Exec: destroy a fence.
/// Caller must prove no pending submission references this fence and exclusive access.
pub fn destroy_fence_exec(
    fence: &mut RuntimeFence,
    pending_submissions: Ghost<Seq<SubmissionRecord>>,
    thread: Ghost<ThreadId>,
    reg: Ghost<TokenRegistry>,
)
    requires
        runtime_fence_wf(&*old(fence)),
        fence_not_pending(old(fence)@.id, pending_submissions@),
        holds_exclusive(reg@, old(fence).handle as nat, thread@),
    ensures
        fence@ == destroy_fence_ghost(old(fence)@),
        !fence@.alive,
{
    fence.state = Ghost(destroy_fence_ghost(fence.state@));
}

// ── Extended Specs & Proofs ──────────────────────────────────────────

/// Fence is signaled.
pub open spec fn is_signaled(fence: &RuntimeFence) -> bool {
    fence@.signaled
}

/// Fence is alive.
pub open spec fn fence_alive(fence: &RuntimeFence) -> bool {
    fence@.alive
}

/// Proof: created fence is well-formed.
pub proof fn lemma_create_fence_wf(id: Ghost<nat>, signaled: bool)
    ensures runtime_fence_wf(&RuntimeFence {
        handle: 0,
        state: Ghost(create_fence_ghost(id@, signaled)),
    }),
{
    lemma_create_fence_well_formed(id@, signaled);
}

/// Proof: reset makes fence unsignaled.
pub proof fn lemma_reset_unsignaled(fence: &RuntimeFence)
    requires runtime_fence_wf(fence),
    ensures !reset_fence_ghost(fence@).signaled,
{
    lemma_reset_makes_unsignaled(fence@);
}

/// Proof: signal makes fence signaled.
pub proof fn lemma_signal_makes_signaled_rt(fence: &RuntimeFence, sub_id: Ghost<nat>)
    requires runtime_fence_wf(fence),
    ensures signal_fence_ghost(fence@, sub_id@).signaled,
{
    lemma_signal_makes_signaled(fence@, sub_id@);
}

/// Proof: destroy makes fence not well-formed.
pub proof fn lemma_destroy_not_wf(fence: &RuntimeFence)
    requires runtime_fence_wf(fence),
    ensures !fence_well_formed(destroy_fence_ghost(fence@)),
{
    lemma_destroy_not_well_formed(fence@);
}

} // verus!
