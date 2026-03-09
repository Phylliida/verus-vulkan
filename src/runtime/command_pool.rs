use vstd::prelude::*;
use crate::command_pool::*;
use crate::lifetime::*;
use crate::sync_token::*;

verus! {

/// Runtime wrapper for a Vulkan command pool.
pub struct RuntimeCommandPool {
    /// Opaque handle (maps to VkCommandPool).
    pub handle: u64,
    /// Ghost model of the command pool state.
    pub state: Ghost<CommandPoolState>,
}

impl View for RuntimeCommandPool {
    type V = CommandPoolState;
    open spec fn view(&self) -> CommandPoolState { self.state@ }
}

/// Well-formedness of the runtime command pool.
pub open spec fn runtime_command_pool_wf(pool: &RuntimeCommandPool) -> bool {
    command_pool_well_formed(pool@)
}

/// Exec: create a command pool.
pub fn create_command_pool_exec(
    id: Ghost<nat>,
    queue_family: Ghost<nat>,
    individual_reset: bool,
) -> (out: RuntimeCommandPool)
    ensures
        out@ == create_command_pool(id@, queue_family@, individual_reset),
        runtime_command_pool_wf(&out),
        pool_empty(out@),
{
    proof { lemma_fresh_pool_well_formed(id@, queue_family@, individual_reset); }
    RuntimeCommandPool {
        handle: 0,
        state: Ghost(create_command_pool(id@, queue_family@, individual_reset)),
    }
}

/// Exec: destroy a command pool.
/// Caller must prove the pool is empty and holds exclusive access.
pub fn destroy_command_pool_exec(
    pool: &mut RuntimeCommandPool,
    pending_submissions: Ghost<Seq<SubmissionRecord>>,
    thread: Ghost<ThreadId>,
    reg: Ghost<TokenRegistry>,
)
    requires
        runtime_command_pool_wf(&*old(pool)),
        pool_empty(old(pool)@),
        // All pending submissions must be completed (CBs from this pool may be in-flight)
        forall|i: int| 0 <= i < pending_submissions@.len()
            ==> (#[trigger] pending_submissions@[i]).completed,
        holds_exclusive(reg@, old(pool)@.id, thread@),
    ensures
        pool@ == destroy_command_pool_ghost(old(pool)@),
        !pool@.alive,
{
    pool.state = Ghost(destroy_command_pool_ghost(pool.state@));
}

/// Exec: reset a command pool (all allocated CBs go to Initial state).
/// Returns the set of CBs that were reset.
pub fn reset_command_pool_exec(
    pool: &RuntimeCommandPool,
    pending_submissions: Ghost<Seq<SubmissionRecord>>,
    thread: Ghost<ThreadId>,
    reg: Ghost<TokenRegistry>,
) -> (out: Ghost<Set<nat>>)
    requires
        runtime_command_pool_wf(pool),
        // All pending submissions must be completed (CBs from this pool may be in-flight)
        forall|i: int| 0 <= i < pending_submissions@.len()
            ==> (#[trigger] pending_submissions@[i]).completed,
        holds_exclusive(reg@, pool@.id, thread@),
    ensures
        out@ == reset_pool_cbs(pool@, thread@, reg@).unwrap(),
{
    Ghost(reset_pool_cbs(pool.state@, thread@, reg@).unwrap())
}

// ── Extended Specs & Proofs ──────────────────────────────────────────

/// Command pool is alive.
pub open spec fn command_pool_alive(pool: &RuntimeCommandPool) -> bool {
    pool@.alive
}

/// Proof: creating a command pool produces an alive pool.
pub proof fn lemma_create_command_pool_alive(
    id: Ghost<nat>,
    queue_family: Ghost<nat>,
    individual_reset: bool,
)
    ensures command_pool_alive(&RuntimeCommandPool {
        handle: 0,
        state: Ghost(create_command_pool(id@, queue_family@, individual_reset)),
    }),
{
    lemma_fresh_pool_well_formed(id@, queue_family@, individual_reset);
}

/// Proof: fresh pool is empty.
pub proof fn lemma_create_command_pool_empty(
    id: Ghost<nat>,
    queue_family: Ghost<nat>,
    individual_reset: bool,
)
    ensures pool_empty(create_command_pool(id@, queue_family@, individual_reset)),
{
    lemma_fresh_pool_empty(id@, queue_family@, individual_reset);
}

/// Proof: destroying a pool preserves its id.
pub proof fn lemma_destroy_command_pool_preserves_id_rt(pool: &RuntimeCommandPool)
    requires runtime_command_pool_wf(pool),
    ensures destroy_command_pool_ghost(pool@).id == pool@.id,
{
}

} // verus!
