use vstd::prelude::*;
use crate::query_pool::*;
use crate::lifetime::*;
use crate::sync_token::*;
use super::device::RuntimeDevice;

verus! {

///  Runtime wrapper for a Vulkan query pool (VkQueryPool).
pub struct RuntimeQueryPool {
    ///  Opaque handle (maps to VkQueryPool).
    pub handle: u64,
    ///  Ghost model of the query pool state.
    pub state: Ghost<QueryPoolState>,
}

impl View for RuntimeQueryPool {
    type V = QueryPoolState;
    open spec fn view(&self) -> QueryPoolState { self.state@ }
}

///  Well-formedness of the runtime query pool.
pub open spec fn runtime_query_pool_wf(pool: &RuntimeQueryPool) -> bool {
    pool@.alive && pool@.query_count > 0
}

///  Exec: create a query pool.
pub fn create_query_pool_exec(
    id: Ghost<nat>,
    count: Ghost<nat>,
) -> (out: RuntimeQueryPool)
    requires count@ > 0,
    ensures
        out@ == create_query_pool(id@, count@),
        runtime_query_pool_wf(&out),
{
    RuntimeQueryPool {
        handle: 0,
        state: Ghost(create_query_pool(id@, count@)),
    }
}

///  Exec: destroy a query pool.
pub fn destroy_query_pool_exec(
    pool: &mut RuntimeQueryPool,
    dev: &RuntimeDevice,
    thread: Ghost<ThreadId>,
    reg: Ghost<TokenRegistry>,
)
    requires
        runtime_query_pool_wf(&*old(pool)),
        forall|i: int| 0 <= i < dev@.pending_submissions.len()
            ==> (#[trigger] dev@.pending_submissions[i]).completed,
        holds_exclusive(reg@, SyncObjectId::Handle(old(pool)@.id), thread@),
    ensures
        pool@ == destroy_query_pool(old(pool)@),
        !pool@.alive,
{
    pool.state = Ghost(destroy_query_pool(pool.state@));
}

///  Exec: reset a range of queries.
pub fn reset_queries_exec(
    pool: &mut RuntimeQueryPool,
    first: Ghost<nat>,
    count: Ghost<nat>,
)
    requires
        runtime_query_pool_wf(&*old(pool)),
        first@ + count@ <= old(pool)@.query_count,
    ensures
        pool@ == reset_queries(old(pool)@, first@, count@),
        runtime_query_pool_wf(pool),
{
    pool.state = Ghost(reset_queries(pool.state@, first@, count@));
}

///  Exec: begin a query.
pub fn begin_query_exec(
    pool: &mut RuntimeQueryPool,
    index: Ghost<nat>,
)
    requires
        begin_query_valid(old(pool)@, index@),
    ensures
        pool@ == begin_query(old(pool)@, index@),
        runtime_query_pool_wf(pool),
{
    pool.state = Ghost(begin_query(pool.state@, index@));
}

///  Exec: end a query.
pub fn end_query_exec(
    pool: &mut RuntimeQueryPool,
    index: Ghost<nat>,
)
    requires
        end_query_valid(old(pool)@, index@),
    ensures
        pool@ == end_query(old(pool)@, index@),
        runtime_query_pool_wf(pool),
{
    pool.state = Ghost(end_query(pool.state@, index@));
}

//  ── Specs & Proofs ──────────────────────────────────────────────────

///  Query pool is alive.
pub open spec fn query_pool_alive(pool: &RuntimeQueryPool) -> bool {
    pool@.alive
}

///  Proof: creating a pool produces an alive pool.
pub proof fn lemma_create_query_pool_alive(id: Ghost<nat>, count: Ghost<nat>)
    ensures query_pool_alive(&RuntimeQueryPool {
        handle: 0,
        state: Ghost(create_query_pool(id@, count@)),
    }),
{
}

///  Proof: destroying a pool preserves its id.
pub proof fn lemma_destroy_query_pool_preserves_id(pool: &RuntimeQueryPool)
    requires runtime_query_pool_wf(pool),
    ensures destroy_query_pool(pool@).id == pool@.id,
{
}

} //  verus!
