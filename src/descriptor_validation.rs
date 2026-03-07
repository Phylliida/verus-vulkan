use vstd::prelude::*;
use crate::descriptor::*;
use crate::recording::*;
use crate::pipeline::*;

verus! {

// ── Spec Functions ──────────────────────────────────────────────────────

/// A descriptor set at set_index is valid for a pipeline if:
/// - The set is bound at that index in the recording state.
/// - The set is fully bound with respect to its layout.
/// - The layout id matches the pipeline's expected layout id at that index.
pub open spec fn descriptor_set_valid_for_pipeline(
    state: RecordingState,
    set_index: nat,
    dset: DescriptorSetState,
    layout: DescriptorSetLayoutState,
    pipeline_layout_id: nat,
) -> bool {
    state.bound_descriptor_sets.contains_key(set_index)
    && state.bound_descriptor_sets[set_index] == dset.id
    && dset.layout_id == pipeline_layout_id
    && descriptor_set_fully_bound(dset, layout)
}

/// All descriptor sets required by a graphics pipeline are valid.
pub open spec fn all_descriptor_sets_valid(
    state: RecordingState,
    pipeline: GraphicsPipelineState,
    dsets: Map<nat, DescriptorSetState>,
    layouts: Map<nat, DescriptorSetLayoutState>,
) -> bool {
    forall|i: int| #![trigger pipeline.descriptor_set_layouts[i]]
        0 <= i < pipeline.descriptor_set_layouts.len()
        ==> {
            let layout_id = pipeline.descriptor_set_layouts[i];
            state.bound_descriptor_sets.contains_key(i as nat)
            && dsets.contains_key(state.bound_descriptor_sets[i as nat])
            && layouts.contains_key(layout_id)
            && dsets[state.bound_descriptor_sets[i as nat]].layout_id == layout_id
            && descriptor_set_fully_bound(
                dsets[state.bound_descriptor_sets[i as nat]],
                layouts[layout_id],
            )
        }
}

/// Writing all bindings in a layout produces a fully-bound descriptor set.
pub open spec fn all_bindings_written(
    dset: DescriptorSetState,
    layout: DescriptorSetLayoutState,
) -> bool {
    forall|i: int| 0 <= i < layout.bindings.len() ==> {
        let b = #[trigger] layout.bindings[i].binding;
        dset.bindings.contains_key(b)
        && !(dset.bindings[b] === DescriptorBinding::Empty)
    }
}

/// Binding a descriptor set at a given index makes that index bound.
pub open spec fn bind_and_check(
    state: RecordingState,
    set_index: nat,
    set_id: nat,
) -> RecordingState {
    bind_descriptor_set(state, set_index, set_id)
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// all_bindings_written is equivalent to descriptor_set_fully_bound.
pub proof fn lemma_all_bindings_written_is_fully_bound(
    dset: DescriptorSetState,
    layout: DescriptorSetLayoutState,
)
    requires all_bindings_written(dset, layout),
    ensures descriptor_set_fully_bound(dset, layout),
{
}

/// After binding a descriptor set, that set index is bound in the state.
pub proof fn lemma_bind_makes_bound(
    state: RecordingState,
    set_index: nat,
    set_id: nat,
)
    ensures
        bind_descriptor_set(state, set_index, set_id)
            .bound_descriptor_sets.contains_key(set_index),
        bind_descriptor_set(state, set_index, set_id)
            .bound_descriptor_sets[set_index] == set_id,
{
}

/// Binding a descriptor set at one index preserves bindings at other indices.
pub proof fn lemma_bind_preserves_other_sets(
    state: RecordingState,
    set_index: nat,
    set_id: nat,
    other_index: nat,
)
    requires
        other_index != set_index,
        state.bound_descriptor_sets.contains_key(other_index),
    ensures
        bind_descriptor_set(state, set_index, set_id)
            .bound_descriptor_sets.contains_key(other_index),
        bind_descriptor_set(state, set_index, set_id)
            .bound_descriptor_sets[other_index]
            == state.bound_descriptor_sets[other_index],
{
}

/// If all_descriptor_sets_valid holds, then descriptor_sets_bound_for_pipeline holds.
pub proof fn lemma_valid_sets_implies_bound_for_pipeline(
    state: RecordingState,
    pipeline: GraphicsPipelineState,
    dsets: Map<nat, DescriptorSetState>,
    layouts: Map<nat, DescriptorSetLayoutState>,
)
    requires all_descriptor_sets_valid(state, pipeline, dsets, layouts),
    ensures descriptor_sets_bound_for_pipeline(state, pipeline.descriptor_set_layouts),
{
    assert forall|i: int| 0 <= i < pipeline.descriptor_set_layouts.len()
        implies #[trigger] state.bound_descriptor_sets.contains_key(i as nat) by {
        // Trigger the quantifier in all_descriptor_sets_valid
        let _ = pipeline.descriptor_set_layouts[i];
    }
}

/// Updating a descriptor binding preserves fully-bound status if the updated
/// binding is non-Empty and the set was already fully bound.
pub proof fn lemma_update_preserves_fully_bound(
    dset: DescriptorSetState,
    layout: DescriptorSetLayoutState,
    binding_num: nat,
    new_binding: DescriptorBinding,
)
    requires
        descriptor_set_fully_bound(dset, layout),
        !(new_binding === DescriptorBinding::Empty),
    ensures
        descriptor_set_fully_bound(
            update_descriptor_binding(dset, binding_num, new_binding),
            layout,
        ),
{
    let new_dset = update_descriptor_binding(dset, binding_num, new_binding);
    assert forall|i: int| 0 <= i < layout.bindings.len()
        implies ({
            let b = #[trigger] layout.bindings[i].binding;
            new_dset.bindings.contains_key(b)
            && !(new_dset.bindings[b] === DescriptorBinding::Empty)
        }) by {
        let b = layout.bindings[i].binding;
        if b == binding_num {
            // Updated binding: new_binding is non-Empty
        } else {
            // Preserved from original dset
            lemma_update_preserves_other_bindings(dset, binding_num, new_binding, b);
        }
    }
}

/// Binding all required descriptor sets satisfies descriptor_sets_bound_for_pipeline.
/// (For a pipeline with N layouts, binding sets at indices 0..N-1 suffices.)
pub proof fn lemma_sequential_binds_satisfy_pipeline(
    state: RecordingState,
    pipeline_layouts: Seq<nat>,
)
    requires
        pipeline_layouts.len() == 0
        || (forall|i: int| 0 <= i < pipeline_layouts.len()
            ==> #[trigger] state.bound_descriptor_sets.contains_key(i as nat)),
    ensures
        descriptor_sets_bound_for_pipeline(state, pipeline_layouts),
{
}

} // verus!
