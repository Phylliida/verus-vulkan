use vstd::prelude::*;
use crate::descriptor::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// A push descriptor set: inline descriptor bindings pushed to a command buffer.
pub struct PushDescriptorSet {
    pub set_index: nat,
    pub bindings: Map<nat, DescriptorBinding>,
    pub layout_id: nat,
}

/// Tracks all push descriptor state for a command buffer.
pub struct PushDescriptorState {
    /// Currently bound push descriptor sets, keyed by set index.
    pub bound_sets: Map<nat, PushDescriptorSet>,
    /// Maximum number of push descriptor sets supported.
    pub max_push_sets: nat,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// Initial push descriptor state: no sets bound.
pub open spec fn initial_push_descriptor_state(max: nat) -> PushDescriptorState {
    PushDescriptorState {
        bound_sets: Map::empty(),
        max_push_sets: max,
    }
}

/// Ghost update: push a descriptor set.
pub open spec fn push_descriptor_set(
    state: PushDescriptorState,
    set: PushDescriptorSet,
) -> PushDescriptorState {
    PushDescriptorState {
        bound_sets: state.bound_sets.insert(set.set_index, set),
        ..state
    }
}

/// A push descriptor operation is valid.
pub open spec fn push_descriptor_valid(
    state: PushDescriptorState,
    set_index: nat,
    binding_count: nat,
) -> bool {
    set_index < state.max_push_sets
    && binding_count > 0
}

/// A push descriptor set satisfies a pipeline layout at a given set index.
pub open spec fn push_set_satisfies_layout(
    set: PushDescriptorSet,
    expected_layout_id: nat,
) -> bool {
    set.layout_id == expected_layout_id
}

/// Whether push descriptors are bound for all sets required by a pipeline.
pub open spec fn push_descriptors_bound_for_pipeline(
    state: PushDescriptorState,
    required_sets: Seq<nat>,
) -> bool {
    forall|i: int| 0 <= i < required_sets.len() ==>
        state.bound_sets.contains_key(i as nat)
        && push_set_satisfies_layout(
            #[trigger] state.bound_sets[i as nat],
            required_sets[i],
        )
}

// ── Lemmas ──────────────────────────────────────────────────────────────

/// Initial state has no bindings.
pub proof fn lemma_initial_no_bindings(max: nat)
    ensures initial_push_descriptor_state(max).bound_sets == Map::<nat, PushDescriptorSet>::empty(),
{
}

/// Pushing overwrites the previous set at the same index.
pub proof fn lemma_push_overwrites(
    state: PushDescriptorState,
    set: PushDescriptorSet,
)
    ensures
        push_descriptor_set(state, set).bound_sets.contains_key(set.set_index),
        push_descriptor_set(state, set).bound_sets[set.set_index] == set,
{
}

/// Pushing preserves sets at other indices.
pub proof fn lemma_push_preserves_other(
    state: PushDescriptorState,
    set: PushDescriptorSet,
    other_index: nat,
)
    requires
        other_index != set.set_index,
        state.bound_sets.contains_key(other_index),
    ensures
        push_descriptor_set(state, set).bound_sets.contains_key(other_index),
        push_descriptor_set(state, set).bound_sets[other_index]
            == state.bound_sets[other_index],
{
}

/// Pushing preserves max_push_sets.
pub proof fn lemma_push_preserves_max(
    state: PushDescriptorState,
    set: PushDescriptorSet,
)
    ensures
        push_descriptor_set(state, set).max_push_sets == state.max_push_sets,
{
}

/// Initial push descriptor state has max set correctly.
pub proof fn lemma_initial_max(max: nat)
    ensures initial_push_descriptor_state(max).max_push_sets == max,
{
}

} // verus!
