use vstd::prelude::*;
use crate::draw_state::*;
use crate::pipeline::DynamicStateKind;

verus! {

///  Runtime draw-state tracker: pure ghost tracking of vertex/index buffer bindings,
///  dynamic state, and push constant ranges during command recording.
pub struct RuntimeDrawState {
    pub state: Ghost<DrawCallState>,
}

///  Well-formedness: trivially true (pure ghost tracking).
pub open spec fn runtime_draw_state_wf(ds: &RuntimeDrawState) -> bool {
    true
}

///  Create an initial (empty) draw state.
pub fn create_draw_state_exec() -> (out: RuntimeDrawState)
    ensures out.state@ == initial_draw_state(),
{
    RuntimeDrawState {
        state: Ghost(initial_draw_state()),
    }
}

///  Bind a vertex buffer to a slot.
pub fn bind_vertex_buffer_exec(
    ds: &mut RuntimeDrawState,
    slot: Ghost<nat>,
    binding: Ghost<VertexBufferBinding>,
)
    ensures ds.state@ == bind_vertex_buffer(old(ds).state@, slot@, binding@),
{
    ds.state = Ghost(bind_vertex_buffer(ds.state@, slot@, binding@));
}

///  Bind an index buffer.
pub fn bind_index_buffer_exec(
    ds: &mut RuntimeDrawState,
    binding: Ghost<IndexBufferBinding>,
)
    ensures ds.state@ == bind_index_buffer(old(ds).state@, binding@),
{
    ds.state = Ghost(bind_index_buffer(ds.state@, binding@));
}

///  Set a dynamic state.
pub fn set_dynamic_state_exec(
    ds: &mut RuntimeDrawState,
    kind: Ghost<DynamicStateKind>,
)
    ensures ds.state@ == set_dynamic_state(old(ds).state@, kind@),
{
    ds.state = Ghost(set_dynamic_state(ds.state@, kind@));
}

///  Set push constants for a range.
pub fn set_push_constants_exec(
    ds: &mut RuntimeDrawState,
    offset: Ghost<nat>,
    size: Ghost<nat>,
)
    ensures ds.state@ == set_push_constants(old(ds).state@, offset@, size@),
{
    ds.state = Ghost(set_push_constants(ds.state@, offset@, size@));
}

//  ── Proofs ──────────────────────────────────────────────────────────

///  Creating a draw state produces an empty (initial) state.
pub proof fn lemma_create_draw_state_initial()
    ensures ({
        let ds = initial_draw_state();
        ds.vertex_bindings == Map::<nat, VertexBufferBinding>::empty()
        && ds.index_binding.is_none()
        && ds.set_dynamic_states == Set::<DynamicStateKind>::empty()
        && ds.push_constant_ranges_set == Set::<(nat, nat)>::empty()
    }),
{
}

///  After binding a vertex buffer, that slot is satisfied.
pub proof fn lemma_bind_vertex_exec_satisfies(
    ds: RuntimeDrawState,
    slot: nat,
    binding: VertexBufferBinding,
)
    ensures
        bind_vertex_buffer(ds.state@, slot, binding)
            .vertex_bindings.contains_key(slot),
{
}

///  After binding an index buffer, the index buffer is bound.
pub proof fn lemma_bind_index_exec_bound(
    ds: RuntimeDrawState,
    binding: IndexBufferBinding,
)
    ensures
        index_buffer_bound(bind_index_buffer(ds.state@, binding)),
{
}

///  After setting a dynamic state, it is in the set.
pub proof fn lemma_set_dynamic_exec_contains(
    ds: RuntimeDrawState,
    kind: DynamicStateKind,
)
    ensures
        set_dynamic_state(ds.state@, kind)
            .set_dynamic_states.contains(kind),
{
}

} //  verus!
