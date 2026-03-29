use vstd::prelude::*;

verus! {

use crate::descriptor::*;
use crate::descriptor_validation::*;
use crate::pipeline::*;
use crate::resource::*;
use crate::pool_ownership::*;
use crate::sync_token::*;
use crate::memory::*;
use crate::recording::*;
use crate::lifetime::*;
use crate::device::*;
use crate::runtime::descriptor::*;
use super::device::RuntimeDevice;

//  ─── Spec functions ────────────────────────────────────────────

///  Combined validity for a descriptor update: alignment + liveness + usage + safe to update.
pub open spec fn validated_descriptor_wf(
    binding: DescriptorBinding,
    desc_type: DescriptorType,
    limits: DeviceLimits,
    buffers: Map<nat, BufferState>,
    images: Map<nat, ImageState>,
    set_id: nat,
    thread: ThreadId,
    reg: TokenRegistry,
    pending: Seq<SubmissionRecord>,
) -> bool {
    descriptor_binding_aligned(binding, desc_type, limits)
    && descriptor_binding_resource_alive(binding, buffers, images)
    && descriptor_binding_usage_valid(binding, desc_type, buffers, images)
    && update_descriptor_safe(set_id, thread, reg, pending)
}

///  Whether a pipeline's descriptor state is fully valid: all sets bound, valid, and resources alive.
pub open spec fn descriptor_update_safe_for_pipeline(
    state: RecordingState,
    pipeline: GraphicsPipelineState,
    ds_states: Map<nat, DescriptorSetState>,
    layouts: Map<nat, DescriptorSetLayoutState>,
    buffers: Map<nat, BufferState>,
    images: Map<nat, ImageState>,
) -> bool {
    all_descriptor_sets_valid(state, pipeline, ds_states, layouts)
    && all_pipeline_descriptor_resources_alive(
        state,
        pipeline,
        ds_states,
        layouts,
        buffers,
        images,
    )
}

///  Batch validity: all updates in a sequence are valid.
pub open spec fn all_updates_valid(
    updates: Seq<DescriptorBinding>,
    desc_types: Seq<DescriptorType>,
    limits: DeviceLimits,
    buffers: Map<nat, BufferState>,
    images: Map<nat, ImageState>,
) -> bool
    recommends updates.len() == desc_types.len(),
{
    forall|i: int|
        #![trigger updates[i]]
        0 <= i < updates.len()
        ==> descriptor_binding_aligned(updates[i], desc_types[i], limits)
            && descriptor_binding_resource_alive(updates[i], buffers, images)
            && descriptor_binding_usage_valid(updates[i], desc_types[i], buffers, images)
}

//  ─── Exec functions ────────────────────────────────────────────

///  Exec: perform a validated buffer descriptor update.
///  Combines alignment, liveness, usage, and update-safety checks.
pub fn validated_buffer_descriptor_update_exec(
    ds: &mut RuntimeDescriptorSet,
    layout: Ghost<DescriptorSetLayoutState>,
    binding_num: Ghost<nat>,
    new_binding: Ghost<DescriptorBinding>,
    desc_type: Ghost<DescriptorType>,
    limits: Ghost<DeviceLimits>,
    thread: Ghost<ThreadId>,
    pool_ownership: Ghost<PoolOwnership>,
    reg: Ghost<TokenRegistry>,
    dev: &RuntimeDevice,
    buffers: Ghost<Map<nat, BufferState>>,
    images: Ghost<Map<nat, ImageState>>,
)
    requires
        //  Standard update preconditions
        old(ds)@.layout_id == layout@.id,
        layout_contains_binding(layout@, binding_num@),
        !(new_binding@ === DescriptorBinding::Empty),
        descriptor_binding_aligned(new_binding@, desc_type@, limits@),
        can_access_child(pool_ownership@, old(ds)@.id, thread@, reg@),
        //  Validation extras
        descriptor_binding_resource_alive(new_binding@, buffers@, images@),
        descriptor_binding_usage_valid(new_binding@, desc_type@, buffers@, images@),
        update_descriptor_safe(old(ds)@.id, thread@, reg@, dev@.pending_submissions),
    ensures
        ds@ == update_descriptor_binding(old(ds)@, binding_num@, new_binding@),
        descriptor_binding_resource_alive(new_binding@, buffers@, images@),
        descriptor_binding_usage_valid(new_binding@, desc_type@, buffers@, images@),
{
    update_descriptor_set_exec(ds, layout, binding_num, new_binding, desc_type, limits, thread, pool_ownership, reg, dev);
}

///  Exec: perform a validated image descriptor update.
pub fn validated_image_descriptor_update_exec(
    ds: &mut RuntimeDescriptorSet,
    layout: Ghost<DescriptorSetLayoutState>,
    binding_num: Ghost<nat>,
    new_binding: Ghost<DescriptorBinding>,
    desc_type: Ghost<DescriptorType>,
    limits: Ghost<DeviceLimits>,
    thread: Ghost<ThreadId>,
    pool_ownership: Ghost<PoolOwnership>,
    reg: Ghost<TokenRegistry>,
    dev: &RuntimeDevice,
    buffers: Ghost<Map<nat, BufferState>>,
    images: Ghost<Map<nat, ImageState>>,
)
    requires
        old(ds)@.layout_id == layout@.id,
        layout_contains_binding(layout@, binding_num@),
        !(new_binding@ === DescriptorBinding::Empty),
        descriptor_binding_aligned(new_binding@, desc_type@, limits@),
        can_access_child(pool_ownership@, old(ds)@.id, thread@, reg@),
        descriptor_binding_resource_alive(new_binding@, buffers@, images@),
        descriptor_binding_usage_valid(new_binding@, desc_type@, buffers@, images@),
        update_descriptor_safe(old(ds)@.id, thread@, reg@, dev@.pending_submissions),
    ensures
        ds@ == update_descriptor_binding(old(ds)@, binding_num@, new_binding@),
        descriptor_binding_resource_alive(new_binding@, buffers@, images@),
        descriptor_binding_usage_valid(new_binding@, desc_type@, buffers@, images@),
{
    update_descriptor_set_exec(ds, layout, binding_num, new_binding, desc_type, limits, thread, pool_ownership, reg, dev);
}

///  Exec: ghost-level check that all pipeline descriptors are valid and alive.
pub fn validate_pipeline_descriptors_exec(
    state: Ghost<RecordingState>,
    pipeline: Ghost<GraphicsPipelineState>,
    ds_states: Ghost<Map<nat, DescriptorSetState>>,
    layouts: Ghost<Map<nat, DescriptorSetLayoutState>>,
    buffers: Ghost<Map<nat, BufferState>>,
    images: Ghost<Map<nat, ImageState>>,
) -> (result: Ghost<bool>)
    ensures
        result@ == descriptor_update_safe_for_pipeline(
            state@, pipeline@, ds_states@, layouts@, buffers@, images@,
        ),
{
    Ghost(descriptor_update_safe_for_pipeline(
        state@, pipeline@, ds_states@, layouts@, buffers@, images@,
    ))
}

//  ─── Proof functions ───────────────────────────────────────────

///  A validated update ensures the binding's resource is alive.
pub proof fn lemma_validated_update_resources_alive(
    binding: DescriptorBinding,
    desc_type: DescriptorType,
    limits: DeviceLimits,
    buffers: Map<nat, BufferState>,
    images: Map<nat, ImageState>,
    set_id: nat,
    thread: ThreadId,
    reg: TokenRegistry,
    pending: Seq<SubmissionRecord>,
)
    requires
        validated_descriptor_wf(binding, desc_type, limits, buffers, images, set_id, thread, reg, pending),
    ensures
        descriptor_binding_resource_alive(binding, buffers, images),
{
    //  Direct from validated_descriptor_wf definition
}

///  A validated update ensures the binding's usage is valid.
pub proof fn lemma_validated_update_usage_valid(
    binding: DescriptorBinding,
    desc_type: DescriptorType,
    limits: DeviceLimits,
    buffers: Map<nat, BufferState>,
    images: Map<nat, ImageState>,
    set_id: nat,
    thread: ThreadId,
    reg: TokenRegistry,
    pending: Seq<SubmissionRecord>,
)
    requires
        validated_descriptor_wf(binding, desc_type, limits, buffers, images, set_id, thread, reg, pending),
    ensures
        descriptor_binding_usage_valid(binding, desc_type, buffers, images),
{
    //  Direct from validated_descriptor_wf definition
}

///  A validated update preserves layout compatibility (the layout_id is unchanged by update).
pub proof fn lemma_validated_update_preserves_layout(
    ds: DescriptorSetState,
    binding_num: nat,
    new_binding: DescriptorBinding,
)
    ensures
        update_descriptor_binding(ds, binding_num, new_binding).layout_id == ds.layout_id,
{
    //  update_descriptor_binding only changes bindings map, not layout_id
}

///  If all pipeline descriptors are valid and alive, then the pipeline is ready for draw.
pub proof fn lemma_pipeline_descriptors_valid_implies_bound(
    state: RecordingState,
    pipeline: GraphicsPipelineState,
    ds_states: Map<nat, DescriptorSetState>,
    layouts: Map<nat, DescriptorSetLayoutState>,
    buffers: Map<nat, BufferState>,
    images: Map<nat, ImageState>,
)
    requires
        descriptor_update_safe_for_pipeline(state, pipeline, ds_states, layouts, buffers, images),
    ensures
        all_descriptor_sets_valid(state, pipeline, ds_states, layouts),
        all_pipeline_descriptor_resources_alive(
            state, pipeline, ds_states, layouts, buffers, images,
        ),
{
    //  Direct from descriptor_update_safe_for_pipeline definition
}

} //  verus!
