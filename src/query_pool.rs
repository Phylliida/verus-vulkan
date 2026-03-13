use vstd::prelude::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// State of a single query within a query pool.
pub enum QuerySlotState {
    /// Query has been reset, ready to begin.
    Reset,
    /// Query is actively recording (between begin and end).
    Active,
    /// Query has completed, results are available.
    Available,
    /// Query is in an undefined state (never reset, or pool just created).
    Uninitialized,
}

/// Ghost state for a Vulkan query pool (VkQueryPool).
pub struct QueryPoolState {
    pub id: nat,
    /// Number of query slots in the pool.
    pub query_count: nat,
    /// State of each query slot.
    pub slot_states: Map<nat, QuerySlotState>,
    /// Whether the pool is alive.
    pub alive: bool,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// Create a fresh query pool with all slots uninitialized.
pub open spec fn create_query_pool(id: nat, count: nat) -> QueryPoolState {
    QueryPoolState {
        id,
        query_count: count,
        slot_states: Map::new(
            |i: nat| i < count,
            |_i: nat| QuerySlotState::Uninitialized,
        ),
        alive: true,
    }
}

/// Reset a range of queries.
pub open spec fn reset_queries(
    pool: QueryPoolState,
    first: nat,
    count: nat,
) -> QueryPoolState
    recommends first + count <= pool.query_count,
{
    QueryPoolState {
        slot_states: Map::new(
            |i: nat| pool.slot_states.contains_key(i),
            |i: nat| {
                if first <= i < first + count {
                    QuerySlotState::Reset
                } else {
                    pool.slot_states[i]
                }
            },
        ),
        ..pool
    }
}

/// Begin a query (start recording).
pub open spec fn begin_query(
    pool: QueryPoolState,
    index: nat,
) -> QueryPoolState
    recommends index < pool.query_count,
{
    QueryPoolState {
        slot_states: pool.slot_states.insert(index, QuerySlotState::Active),
        ..pool
    }
}

/// End a query (stop recording, results become available).
pub open spec fn end_query(
    pool: QueryPoolState,
    index: nat,
) -> QueryPoolState
    recommends index < pool.query_count,
{
    QueryPoolState {
        slot_states: pool.slot_states.insert(index, QuerySlotState::Available),
        ..pool
    }
}

/// A query slot is in the Reset state (ready to begin).
pub open spec fn query_is_reset(pool: QueryPoolState, index: nat) -> bool {
    pool.slot_states.contains_key(index)
    && pool.slot_states[index] == QuerySlotState::Reset
}

/// A query slot is Active (between begin and end).
pub open spec fn query_is_active(pool: QueryPoolState, index: nat) -> bool {
    pool.slot_states.contains_key(index)
    && pool.slot_states[index] == QuerySlotState::Active
}

/// A query slot has available results.
pub open spec fn query_is_available(pool: QueryPoolState, index: nat) -> bool {
    pool.slot_states.contains_key(index)
    && pool.slot_states[index] == QuerySlotState::Available
}

/// Begin query is valid: slot must be Reset.
pub open spec fn begin_query_valid(pool: QueryPoolState, index: nat) -> bool {
    pool.alive && index < pool.query_count && query_is_reset(pool, index)
}

/// End query is valid: slot must be Active.
pub open spec fn end_query_valid(pool: QueryPoolState, index: nat) -> bool {
    pool.alive && index < pool.query_count && query_is_active(pool, index)
}

/// Get results is valid: all slots in range must be Available.
pub open spec fn get_results_valid(
    pool: QueryPoolState,
    first: nat,
    count: nat,
) -> bool {
    pool.alive
    && first + count <= pool.query_count
    && (forall|i: nat| first <= i < first + count
        ==> query_is_available(pool, i))
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// After reset, a query slot is in the Reset state.
pub proof fn lemma_reset_makes_reset(
    pool: QueryPoolState,
    first: nat,
    count: nat,
    index: nat,
)
    requires
        pool.slot_states.contains_key(index),
        first + count <= pool.query_count,
        first <= index < first + count,
    ensures
        query_is_reset(reset_queries(pool, first, count), index),
{
    let result = reset_queries(pool, first, count);
    assert(result.slot_states.contains_key(index));
    assert(result.slot_states[index] == QuerySlotState::Reset);
}

/// The full lifecycle Reset → begin → end produces Available.
pub proof fn lemma_full_lifecycle_available(
    pool: QueryPoolState,
    first: nat,
    count: nat,
    index: nat,
)
    requires
        pool.alive,
        first + count <= pool.query_count,
        first <= index < first + count,
    ensures ({
        let after_reset = reset_queries(pool, first, count);
        let after_begin = begin_query(after_reset, index);
        let after_end = end_query(after_begin, index);
        query_is_available(after_end, index)
    }),
{
}

/// Reset does not affect queries outside the range.
pub proof fn lemma_reset_preserves_outside(
    pool: QueryPoolState,
    first: nat,
    count: nat,
    index: nat,
)
    requires
        first + count <= pool.query_count,
        pool.slot_states.contains_key(index),
        !(first <= index < first + count),
    ensures
        reset_queries(pool, first, count).slot_states[index]
            == pool.slot_states[index],
{
}

/// Begin query changes only the targeted slot.
pub proof fn lemma_begin_preserves_others(
    pool: QueryPoolState,
    index: nat,
    other: nat,
)
    requires
        index != other,
        pool.slot_states.contains_key(other),
    ensures
        begin_query(pool, index).slot_states[other]
            == pool.slot_states[other],
{
}

/// A fresh pool has all slots uninitialized.
pub proof fn lemma_fresh_pool_uninitialized(id: nat, count: nat, index: nat)
    requires index < count,
    ensures
        create_query_pool(id, count).slot_states[index]
            == QuerySlotState::Uninitialized,
{
}

/// Get results on a single available slot is valid.
pub proof fn lemma_single_available_results_valid(
    pool: QueryPoolState,
    index: nat,
)
    requires
        pool.alive,
        index < pool.query_count,
        query_is_available(pool, index),
    ensures
        get_results_valid(pool, index, 1),
{
}

/// After begin_query, the slot is Active.
pub proof fn lemma_begin_makes_active(pool: QueryPoolState, index: nat)
    requires
        pool.slot_states.contains_key(index),
        index < pool.query_count,
    ensures query_is_active(begin_query(pool, index), index),
{
}

/// After end_query, the slot is Available.
pub proof fn lemma_end_makes_available(pool: QueryPoolState, index: nat)
    requires
        pool.slot_states.contains_key(index),
        index < pool.query_count,
    ensures query_is_available(end_query(pool, index), index),
{
}

/// End query changes only the targeted slot.
pub proof fn lemma_end_preserves_others(
    pool: QueryPoolState, index: nat, other: nat,
)
    requires
        index != other,
        pool.slot_states.contains_key(other),
    ensures
        end_query(pool, index).slot_states[other] == pool.slot_states[other],
{
}

/// Write timestamp is valid: slot must be Reset.
pub open spec fn write_timestamp_valid(pool: QueryPoolState, index: nat) -> bool {
    pool.alive && index < pool.query_count && query_is_reset(pool, index)
}

/// Ghost update: write a timestamp (transitions Reset → Available).
pub open spec fn write_timestamp(
    pool: QueryPoolState,
    index: nat,
) -> QueryPoolState
    recommends index < pool.query_count,
{
    QueryPoolState {
        slot_states: pool.slot_states.insert(index, QuerySlotState::Available),
        ..pool
    }
}

/// After write_timestamp, the slot is Available.
pub proof fn lemma_write_timestamp_makes_available(pool: QueryPoolState, index: nat)
    requires
        pool.slot_states.contains_key(index),
        index < pool.query_count,
    ensures query_is_available(write_timestamp(pool, index), index),
{
}

/// Destroy a query pool.
pub open spec fn destroy_query_pool(pool: QueryPoolState) -> QueryPoolState {
    QueryPoolState {
        alive: false,
        ..pool
    }
}

/// A fresh pool is alive.
pub proof fn lemma_fresh_pool_alive(id: nat, count: nat)
    ensures create_query_pool(id, count).alive,
{
}

/// Destroying a pool makes it not alive.
pub proof fn lemma_destroy_not_alive(pool: QueryPoolState)
    ensures !destroy_query_pool(pool).alive,
{
}

/// Destroying a pool preserves its id.
pub proof fn lemma_destroy_preserves_id(pool: QueryPoolState)
    ensures destroy_query_pool(pool).id == pool.id,
{
}

} // verus!
