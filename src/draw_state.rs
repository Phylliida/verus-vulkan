use vstd::prelude::*;
use crate::recording::*;
use crate::pipeline::*;
use crate::render_pass::*;
use crate::shader_interface::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// Binding of a vertex buffer to a slot.
pub struct VertexBufferBinding {
    pub buffer_id: nat,
    pub offset: nat,
    pub stride: nat,
}

/// Binding of an index buffer.
pub struct IndexBufferBinding {
    pub buffer_id: nat,
    pub offset: nat,
    /// 0 = U16, 1 = U32.
    pub index_type: nat,
}

/// Kinds of dynamic state that can be declared by a pipeline.
pub enum DynamicStateKind {
    Viewport,
    Scissor,
    LineWidth,
    DepthBias,
    BlendConstants,
    DepthBounds,
    StencilCompareMask,
    StencilWriteMask,
    StencilReference,
}

/// Extended draw-call state tracked during recording, beyond what
/// RecordingState captures. This tracks vertex/index buffer bindings,
/// dynamic state, and push constant ranges.
pub struct DrawCallState {
    /// Bound vertex buffer bindings, indexed by binding slot.
    pub vertex_bindings: Map<nat, VertexBufferBinding>,
    /// Bound index buffer, if any.
    pub index_binding: Option<IndexBufferBinding>,
    /// Set of dynamic states that have been set via vkCmdSet* commands.
    pub set_dynamic_states: Set<DynamicStateKind>,
    /// Push constant byte ranges that have been written.
    /// Tracked as a set of (offset, size) pairs.
    pub push_constant_ranges_set: Set<(nat, nat)>,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// Initial draw call state: nothing bound.
pub open spec fn initial_draw_state() -> DrawCallState {
    DrawCallState {
        vertex_bindings: Map::empty(),
        index_binding: None,
        set_dynamic_states: Set::empty(),
        push_constant_ranges_set: Set::empty(),
    }
}

/// Bind a vertex buffer to a slot.
pub open spec fn bind_vertex_buffer(
    state: DrawCallState,
    slot: nat,
    binding: VertexBufferBinding,
) -> DrawCallState {
    DrawCallState {
        vertex_bindings: state.vertex_bindings.insert(slot, binding),
        ..state
    }
}

/// Bind an index buffer.
pub open spec fn bind_index_buffer(
    state: DrawCallState,
    binding: IndexBufferBinding,
) -> DrawCallState {
    DrawCallState {
        index_binding: Some(binding),
        ..state
    }
}

/// Set a dynamic state.
pub open spec fn set_dynamic_state(
    state: DrawCallState,
    kind: DynamicStateKind,
) -> DrawCallState {
    DrawCallState {
        set_dynamic_states: state.set_dynamic_states.insert(kind),
        ..state
    }
}

/// Set push constants for a range.
pub open spec fn set_push_constants(
    state: DrawCallState,
    offset: nat,
    size: nat,
) -> DrawCallState {
    DrawCallState {
        push_constant_ranges_set: state.push_constant_ranges_set.insert((offset, size)),
        ..state
    }
}

/// All required vertex buffer binding slots are bound.
pub open spec fn vertex_bindings_satisfied(
    state: DrawCallState,
    required_slots: Set<nat>,
) -> bool {
    forall|slot: nat| required_slots.contains(slot)
        ==> state.vertex_bindings.contains_key(slot)
}

/// An index buffer is bound (required for DrawIndexed).
pub open spec fn index_buffer_bound(state: DrawCallState) -> bool {
    state.index_binding.is_some()
}

/// All required dynamic states have been set.
pub open spec fn dynamic_states_satisfied(
    state: DrawCallState,
    required: Set<DynamicStateKind>,
) -> bool {
    required.subset_of(state.set_dynamic_states)
}

/// A push constant range is covered by a previously set range.
pub open spec fn push_constant_range_covered(
    state: DrawCallState,
    offset: nat,
    size: nat,
) -> bool {
    state.push_constant_ranges_set.contains((offset, size))
}

/// All push constant ranges required by the pipeline are covered.
pub open spec fn all_push_constants_covered(
    state: DrawCallState,
    ranges: Seq<PushConstantRange>,
) -> bool {
    forall|i: int| 0 <= i < ranges.len() ==>
        push_constant_range_covered(state, (#[trigger] ranges[i]).offset, ranges[i].size)
}

/// Full draw call validation: recording state + draw state + pipeline.
pub open spec fn full_draw_valid(
    rec_state: RecordingState,
    draw_state: DrawCallState,
    pipeline: GraphicsPipelineState,
    rp: RenderPassState,
    required_vertex_slots: Set<nat>,
    required_dynamic_states: Set<DynamicStateKind>,
    push_constant_ranges: Seq<PushConstantRange>,
) -> bool {
    draw_call_valid(rec_state, pipeline, rp)
    && vertex_bindings_satisfied(draw_state, required_vertex_slots)
    && dynamic_states_satisfied(draw_state, required_dynamic_states)
    && all_push_constants_covered(draw_state, push_constant_ranges)
}

/// Full draw-indexed validation: same as draw + index buffer bound.
pub open spec fn full_draw_indexed_valid(
    rec_state: RecordingState,
    draw_state: DrawCallState,
    pipeline: GraphicsPipelineState,
    rp: RenderPassState,
    required_vertex_slots: Set<nat>,
    required_dynamic_states: Set<DynamicStateKind>,
    push_constant_ranges: Seq<PushConstantRange>,
) -> bool {
    full_draw_valid(rec_state, draw_state, pipeline, rp,
        required_vertex_slots, required_dynamic_states, push_constant_ranges)
    && index_buffer_bound(draw_state)
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// Binding a vertex buffer satisfies that slot's requirement.
pub proof fn lemma_bind_satisfies_slot(
    state: DrawCallState,
    slot: nat,
    binding: VertexBufferBinding,
)
    ensures
        bind_vertex_buffer(state, slot, binding)
            .vertex_bindings.contains_key(slot),
{
}

/// Binding a vertex buffer preserves other slots.
pub proof fn lemma_bind_preserves_other_slots(
    state: DrawCallState,
    slot: nat,
    binding: VertexBufferBinding,
    other: nat,
)
    requires
        other != slot,
        state.vertex_bindings.contains_key(other),
    ensures
        bind_vertex_buffer(state, slot, binding)
            .vertex_bindings.contains_key(other),
        bind_vertex_buffer(state, slot, binding)
            .vertex_bindings[other] == state.vertex_bindings[other],
{
}

/// Binding an index buffer makes it bound.
pub proof fn lemma_bind_index_buffer_bound(
    state: DrawCallState,
    binding: IndexBufferBinding,
)
    ensures
        index_buffer_bound(bind_index_buffer(state, binding)),
{
}

/// Setting a dynamic state satisfies that requirement.
pub proof fn lemma_set_dynamic_satisfies(
    state: DrawCallState,
    kind: DynamicStateKind,
)
    ensures
        set_dynamic_state(state, kind)
            .set_dynamic_states.contains(kind),
{
}

/// Setting a dynamic state preserves previously set states.
pub proof fn lemma_set_dynamic_preserves_others(
    state: DrawCallState,
    kind: DynamicStateKind,
    other: DynamicStateKind,
)
    requires state.set_dynamic_states.contains(other),
    ensures
        set_dynamic_state(state, kind)
            .set_dynamic_states.contains(other),
{
}

/// If all required dynamic states are in the set, satisfaction holds.
pub proof fn lemma_dynamic_subset_satisfied(
    state: DrawCallState,
    required: Set<DynamicStateKind>,
)
    requires required.subset_of(state.set_dynamic_states),
    ensures dynamic_states_satisfied(state, required),
{
}

/// Setting push constants covers that range.
pub proof fn lemma_push_constants_covers_set_range(
    state: DrawCallState,
    offset: nat,
    size: nat,
)
    ensures
        push_constant_range_covered(
            set_push_constants(state, offset, size),
            offset,
            size,
        ),
{
}

/// An empty required vertex slots set is trivially satisfied.
pub proof fn lemma_empty_vertex_slots_satisfied(state: DrawCallState)
    ensures vertex_bindings_satisfied(state, Set::empty()),
{
}

/// An empty push constant ranges sequence is trivially covered.
pub proof fn lemma_empty_push_constants_covered(state: DrawCallState)
    ensures all_push_constants_covered(state, Seq::empty()),
{
}

/// An empty dynamic state requirement is trivially satisfied.
pub proof fn lemma_empty_dynamic_satisfied(state: DrawCallState)
    ensures dynamic_states_satisfied(state, Set::empty()),
{
    assert(Set::<DynamicStateKind>::empty().subset_of(state.set_dynamic_states));
}

} // verus!
