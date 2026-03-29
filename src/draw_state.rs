use vstd::prelude::*;
use crate::recording::*;
use crate::pipeline::*;
use crate::render_pass::*;
use crate::shader_interface::*;

verus! {

//  ── Types ───────────────────────────────────────────────────────────────

///  Binding of a vertex buffer to a slot.
pub struct VertexBufferBinding {
    pub buffer_id: nat,
    pub offset: nat,
    pub stride: nat,
    ///  Size of the bound buffer in bytes.
    pub buffer_size: nat,
}

///  Binding of an index buffer.
pub struct IndexBufferBinding {
    pub buffer_id: nat,
    pub offset: nat,
    ///  0 = U16, 1 = U32.
    pub index_type: nat,
    ///  Size of the bound buffer in bytes.
    pub buffer_size: nat,
}

///  Extended draw-call state tracked during recording, beyond what
///  RecordingState captures. This tracks vertex/index buffer bindings,
///  dynamic state, and push constant ranges.
pub struct DrawCallState {
    ///  Bound vertex buffer bindings, indexed by binding slot.
    pub vertex_bindings: Map<nat, VertexBufferBinding>,
    ///  Bound index buffer, if any.
    pub index_binding: Option<IndexBufferBinding>,
    ///  Set of dynamic states that have been set via vkCmdSet* commands.
    pub set_dynamic_states: Set<DynamicStateKind>,
    ///  Push constant byte ranges that have been written.
    ///  Tracked as a set of (offset, size) pairs.
    pub push_constant_ranges_set: Set<(nat, nat)>,
}

//  ── Spec Functions ──────────────────────────────────────────────────────

///  Initial draw call state: nothing bound.
pub open spec fn initial_draw_state() -> DrawCallState {
    DrawCallState {
        vertex_bindings: Map::empty(),
        index_binding: None,
        set_dynamic_states: Set::empty(),
        push_constant_ranges_set: Set::empty(),
    }
}

///  Bind a vertex buffer to a slot.
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

///  Bind an index buffer.
pub open spec fn bind_index_buffer(
    state: DrawCallState,
    binding: IndexBufferBinding,
) -> DrawCallState {
    DrawCallState {
        index_binding: Some(binding),
        ..state
    }
}

///  Set a dynamic state.
pub open spec fn set_dynamic_state(
    state: DrawCallState,
    kind: DynamicStateKind,
) -> DrawCallState {
    DrawCallState {
        set_dynamic_states: state.set_dynamic_states.insert(kind),
        ..state
    }
}

///  Set a dynamic state, validated against the pipeline's declared dynamic states.
///  Callers should prefer this over `set_dynamic_state` to ensure only
///  pipeline-declared dynamic states are set.
pub open spec fn set_dynamic_state_validated(
    state: DrawCallState,
    kind: DynamicStateKind,
    pipeline_dynamic_states: Set<DynamicStateKind>,
) -> DrawCallState
    recommends pipeline_dynamic_states.contains(kind),
{
    DrawCallState {
        set_dynamic_states: state.set_dynamic_states.insert(kind),
        ..state
    }
}

///  Set push constants for a range.
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

///  All required vertex buffer binding slots are bound.
pub open spec fn vertex_bindings_satisfied(
    state: DrawCallState,
    required_slots: Set<nat>,
) -> bool {
    forall|slot: nat| required_slots.contains(slot)
        ==> state.vertex_bindings.contains_key(slot)
}

///  An index buffer is bound (required for DrawIndexed).
pub open spec fn index_buffer_bound(state: DrawCallState) -> bool {
    state.index_binding.is_some()
}

///  All required dynamic states have been set.
pub open spec fn dynamic_states_satisfied(
    state: DrawCallState,
    required: Set<DynamicStateKind>,
) -> bool {
    required.subset_of(state.set_dynamic_states)
}

///  A push constant range is covered by a previously set range.
pub open spec fn push_constant_range_covered(
    state: DrawCallState,
    offset: nat,
    size: nat,
) -> bool {
    state.push_constant_ranges_set.contains((offset, size))
}

///  All push constant ranges required by the pipeline are covered.
pub open spec fn all_push_constants_covered(
    state: DrawCallState,
    ranges: Seq<PushConstantRange>,
) -> bool {
    forall|i: int| 0 <= i < ranges.len() ==>
        push_constant_range_covered(state, (#[trigger] ranges[i]).offset, ranges[i].size)
}

//  ── Buffer Bounds Specs ─────────────────────────────────────────────────

///  Size in bytes of a single index given the index type (0=U16, 1=U32).
pub open spec fn index_type_size(index_type: nat) -> nat {
    if index_type == 0 { 2 } else { 4 }
}

///  Vertex draw is within the bounds of all required vertex buffer bindings.
///  For each required slot, (first_vertex + vertex_count) * stride + offset <= buffer_size.
pub open spec fn vertex_draw_in_bounds(
    state: DrawCallState,
    required_slots: Set<nat>,
    first_vertex: nat,
    vertex_count: nat,
) -> bool {
    forall|slot: nat| required_slots.contains(slot)
        && state.vertex_bindings.contains_key(slot)
        ==> {
            let b = state.vertex_bindings[slot];
            b.stride > 0
            && b.offset + (first_vertex + vertex_count) * b.stride <= b.buffer_size
        }
}

///  Indexed draw is within the bounds of the index buffer.
///  offset + (first_index + index_count) * index_element_size <= buffer_size.
pub open spec fn indexed_draw_in_bounds(
    state: DrawCallState,
    first_index: nat,
    index_count: nat,
) -> bool {
    state.index_binding.is_some()
    && {
        let ib = state.index_binding.unwrap();
        ib.offset + (first_index + index_count) * index_type_size(ib.index_type) <= ib.buffer_size
    }
}

//  ── Full Draw Validation ────────────────────────────────────────────────

///  Full draw call validation: recording state + draw state + pipeline + bounds.
///  Dynamic states are derived from the pipeline's required_dynamic_states field.
pub open spec fn full_draw_valid(
    rec_state: RecordingState,
    draw_state: DrawCallState,
    pipeline: GraphicsPipelineState,
    rp: RenderPassState,
    required_vertex_slots: Set<nat>,
    push_constant_ranges: Seq<PushConstantRange>,
    first_vertex: nat,
    vertex_count: nat,
) -> bool {
    draw_call_valid(rec_state, pipeline, rp)
    && vertex_bindings_satisfied(draw_state, required_vertex_slots)
    && dynamic_states_satisfied(draw_state, pipeline.required_dynamic_states)
    && all_push_constants_covered(draw_state, push_constant_ranges)
    && vertex_draw_in_bounds(draw_state, required_vertex_slots, first_vertex, vertex_count)
}

///  Full draw-indexed validation: same as draw + index buffer bound + index bounds.
pub open spec fn full_draw_indexed_valid(
    rec_state: RecordingState,
    draw_state: DrawCallState,
    pipeline: GraphicsPipelineState,
    rp: RenderPassState,
    required_vertex_slots: Set<nat>,
    push_constant_ranges: Seq<PushConstantRange>,
    first_vertex: nat,
    vertex_count: nat,
    first_index: nat,
    index_count: nat,
) -> bool {
    full_draw_valid(rec_state, draw_state, pipeline, rp,
        required_vertex_slots, push_constant_ranges, first_vertex, vertex_count)
    && index_buffer_bound(draw_state)
    && indexed_draw_in_bounds(draw_state, first_index, index_count)
}

//  ── Proofs ──────────────────────────────────────────────────────────────

///  Binding a vertex buffer satisfies that slot's requirement.
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

///  Binding a vertex buffer preserves other slots.
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

///  Binding an index buffer makes it bound.
pub proof fn lemma_bind_index_buffer_bound(
    state: DrawCallState,
    binding: IndexBufferBinding,
)
    ensures
        index_buffer_bound(bind_index_buffer(state, binding)),
{
}

///  Setting a dynamic state satisfies that requirement.
pub proof fn lemma_set_dynamic_satisfies(
    state: DrawCallState,
    kind: DynamicStateKind,
)
    ensures
        set_dynamic_state(state, kind)
            .set_dynamic_states.contains(kind),
{
}

///  Setting a validated dynamic state ensures it is in the pipeline's declared states.
pub proof fn lemma_validated_dynamic_state_in_pipeline(
    state: DrawCallState,
    kind: DynamicStateKind,
    pipeline_dynamic_states: Set<DynamicStateKind>,
)
    requires pipeline_dynamic_states.contains(kind),
    ensures
        set_dynamic_state_validated(state, kind, pipeline_dynamic_states)
            .set_dynamic_states.contains(kind),
{
}

///  Setting a dynamic state preserves previously set states.
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

///  If all required dynamic states are in the set, satisfaction holds.
pub proof fn lemma_dynamic_subset_satisfied(
    state: DrawCallState,
    required: Set<DynamicStateKind>,
)
    requires required.subset_of(state.set_dynamic_states),
    ensures dynamic_states_satisfied(state, required),
{
}

///  Setting push constants covers that range.
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

///  An empty required vertex slots set is trivially satisfied.
pub proof fn lemma_empty_vertex_slots_satisfied(state: DrawCallState)
    ensures vertex_bindings_satisfied(state, Set::empty()),
{
}

///  An empty push constant ranges sequence is trivially covered.
pub proof fn lemma_empty_push_constants_covered(state: DrawCallState)
    ensures all_push_constants_covered(state, Seq::empty()),
{
}

///  An empty dynamic state requirement is trivially satisfied.
pub proof fn lemma_empty_dynamic_satisfied(state: DrawCallState)
    ensures dynamic_states_satisfied(state, Set::empty()),
{
    assert(Set::<DynamicStateKind>::empty().subset_of(state.set_dynamic_states));
}

///  A pipeline with no required dynamic states has trivially satisfied requirements.
pub proof fn lemma_no_required_dynamic_trivial(
    state: DrawCallState,
    pipeline: GraphicsPipelineState,
)
    requires pipeline.required_dynamic_states == Set::<DynamicStateKind>::empty(),
    ensures dynamic_states_satisfied(state, pipeline.required_dynamic_states),
{
    assert(Set::<DynamicStateKind>::empty().subset_of(state.set_dynamic_states));
}

///  Setting viewport and scissor satisfies a pipeline that requires only those two.
pub proof fn lemma_viewport_scissor_dynamic_sufficient(
    state: DrawCallState,
    pipeline: GraphicsPipelineState,
)
    requires
        state.set_dynamic_states.contains(DynamicStateKind::Viewport),
        state.set_dynamic_states.contains(DynamicStateKind::Scissor),
        pipeline.required_dynamic_states == Set::<DynamicStateKind>::empty()
            .insert(DynamicStateKind::Viewport)
            .insert(DynamicStateKind::Scissor),
    ensures
        dynamic_states_satisfied(state, pipeline.required_dynamic_states),
{
}

//  ── Buffer Bounds Lemmas ────────────────────────────────────────────────

///  With no required vertex slots, vertex bounds are trivially satisfied.
pub proof fn lemma_zero_vertex_count_in_bounds(
    state: DrawCallState, first_vertex: nat, vertex_count: nat,
)
    ensures vertex_draw_in_bounds(state, Set::<nat>::empty(), first_vertex, vertex_count),
{
}

///  Zero index count from the start is always in bounds (no data consumed).
pub proof fn lemma_zero_index_count_in_bounds(
    state: DrawCallState,
)
    requires
        state.index_binding.is_some(),
        state.index_binding.unwrap().offset <= state.index_binding.unwrap().buffer_size,
    ensures indexed_draw_in_bounds(state, 0, 0),
{
}

///  U16 index type has size 2.
pub proof fn lemma_u16_index_size()
    ensures index_type_size(0) == 2,
{
}

///  U32 index type has size 4.
pub proof fn lemma_u32_index_size()
    ensures index_type_size(1) == 4,
{
}

///  Binding a vertex buffer with sufficient size enables bounds checking.
pub proof fn lemma_bind_vertex_enables_bounds(
    state: DrawCallState, slot: nat, binding: VertexBufferBinding,
    first_vertex: nat, vertex_count: nat,
)
    requires
        binding.stride > 0,
        binding.offset + (first_vertex + vertex_count) * binding.stride <= binding.buffer_size,
    ensures ({
        let new_state = bind_vertex_buffer(state, slot, binding);
        let b = new_state.vertex_bindings[slot];
        b.offset + (first_vertex + vertex_count) * b.stride <= b.buffer_size
    }),
{
}

///  Empty required vertex slots make bounds trivially satisfied.
pub proof fn lemma_empty_slots_bounds_trivial(
    state: DrawCallState, first_vertex: nat, vertex_count: nat,
)
    ensures vertex_draw_in_bounds(state, Set::empty(), first_vertex, vertex_count),
{
}

} //  verus!
