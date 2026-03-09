use vstd::prelude::*;
use crate::descriptor::*;
use crate::device::*;
use crate::image_layout::*;
use crate::recording::*;
use crate::pipeline::*;
use crate::memory::*;
use crate::flags::*;
use crate::sync_token::*;
use crate::lifetime::*;
use crate::resource::*;

verus! {

// ── Alignment Specs ─────────────────────────────────────────────────────

/// Whether `offset` is a multiple of `alignment`.
pub open spec fn is_aligned(offset: nat, alignment: nat) -> bool
    recommends alignment > 0,
{
    offset % alignment == 0
}

/// Whether a buffer descriptor offset is correctly aligned for its type.
pub open spec fn buffer_offset_aligned(
    offset: nat,
    desc_type: DescriptorType,
    limits: DeviceLimits,
) -> bool {
    match desc_type {
        DescriptorType::UniformBuffer =>
            is_aligned(offset, limits.min_uniform_buffer_offset_alignment),
        DescriptorType::StorageBuffer =>
            is_aligned(offset, limits.min_storage_buffer_offset_alignment),
        DescriptorType::UniformBufferDynamic =>
            is_aligned(offset, limits.min_uniform_buffer_offset_alignment),
        DescriptorType::StorageBufferDynamic =>
            is_aligned(offset, limits.min_storage_buffer_offset_alignment),
        _ => true,
    }
}

/// Whether a descriptor binding's buffer offset is aligned for the given type.
pub open spec fn descriptor_binding_aligned(
    binding: DescriptorBinding,
    desc_type: DescriptorType,
    limits: DeviceLimits,
) -> bool {
    match binding {
        DescriptorBinding::BoundBuffer { buffer_id: _, offset, range: _ } =>
            buffer_offset_aligned(offset, desc_type, limits),
        _ => true,
    }
}

// ── Alignment Lemmas ────────────────────────────────────────────────────

/// Zero offset is always aligned (for any positive alignment).
pub proof fn lemma_zero_offset_aligned(alignment: nat)
    requires alignment > 0,
    ensures is_aligned(0, alignment),
{
}

/// Image bindings are always considered aligned (alignment is a buffer concept).
pub proof fn lemma_image_binding_always_aligned(
    image_id: nat, layout: ImageLayout,
    desc_type: DescriptorType, limits: DeviceLimits,
)
    ensures descriptor_binding_aligned(
        DescriptorBinding::BoundImage { image_id, layout },
        desc_type, limits,
    ),
{
}

/// A multiple of the alignment is aligned.
pub proof fn lemma_multiple_aligned(k: nat, alignment: nat)
    requires alignment > 0,
    ensures is_aligned(k * alignment, alignment),
{
    assert((k * alignment) % alignment == 0) by (nonlinear_arith)
        requires alignment > 0;
}

/// Non-buffer descriptor types (images, samplers) have trivially aligned offsets.
pub proof fn lemma_non_buffer_type_always_aligned(
    offset: nat, limits: DeviceLimits,
)
    ensures
        buffer_offset_aligned(offset, DescriptorType::SampledImage, limits),
        buffer_offset_aligned(offset, DescriptorType::StorageImage, limits),
        buffer_offset_aligned(offset, DescriptorType::CombinedImageSampler, limits),
        buffer_offset_aligned(offset, DescriptorType::InputAttachment, limits),
{
}

// ── Dynamic Offset Validation ───────────────────────────────────────────

/// Whether a descriptor type is a dynamic buffer type.
pub open spec fn is_dynamic_descriptor_type(desc_type: DescriptorType) -> bool {
    matches!(desc_type, DescriptorType::UniformBufferDynamic | DescriptorType::StorageBufferDynamic)
}

/// Whether a dynamic offset is correctly aligned for its descriptor type.
pub open spec fn dynamic_offset_aligned(
    offset: nat,
    desc_type: DescriptorType,
    limits: DeviceLimits,
) -> bool {
    match desc_type {
        DescriptorType::UniformBufferDynamic =>
            is_aligned(offset, limits.min_uniform_buffer_offset_alignment),
        DescriptorType::StorageBufferDynamic =>
            is_aligned(offset, limits.min_storage_buffer_offset_alignment),
        _ => true,
    }
}

/// Whether a dynamic offset keeps the access within the buffer bounds.
pub open spec fn dynamic_offset_in_bounds(
    static_offset: nat,
    dynamic_offset: nat,
    range: nat,
    buffer_size: nat,
) -> bool {
    static_offset + dynamic_offset + range <= buffer_size
}

/// Zero dynamic offset is always aligned (for any descriptor type with positive alignment).
pub proof fn lemma_zero_dynamic_offset_valid(
    desc_type: DescriptorType,
    limits: DeviceLimits,
)
    requires
        limits.min_uniform_buffer_offset_alignment > 0,
        limits.min_storage_buffer_offset_alignment > 0,
    ensures dynamic_offset_aligned(0, desc_type, limits),
{
    lemma_zero_offset_aligned(limits.min_uniform_buffer_offset_alignment);
    lemma_zero_offset_aligned(limits.min_storage_buffer_offset_alignment);
}

/// Zero dynamic offset preserves buffer bounds (if static offset + range <= buffer_size).
pub proof fn lemma_zero_dynamic_offset_in_bounds(
    static_offset: nat,
    range: nat,
    buffer_size: nat,
)
    requires static_offset + range <= buffer_size,
    ensures dynamic_offset_in_bounds(static_offset, 0, range, buffer_size),
{
}

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
    layout_id: nat,
) -> RecordingState {
    bind_descriptor_set(state, set_index, set_id, layout_id, Seq::empty())
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
    layout_id: nat,
    dynamic_offsets: Seq<nat>,
)
    ensures
        bind_descriptor_set(state, set_index, set_id, layout_id, dynamic_offsets)
            .bound_descriptor_sets.contains_key(set_index),
        bind_descriptor_set(state, set_index, set_id, layout_id, dynamic_offsets)
            .bound_descriptor_sets[set_index] == set_id,
        bind_descriptor_set(state, set_index, set_id, layout_id, dynamic_offsets)
            .bound_set_layouts.contains_key(set_index),
        bind_descriptor_set(state, set_index, set_id, layout_id, dynamic_offsets)
            .bound_set_layouts[set_index] == layout_id,
        bind_descriptor_set(state, set_index, set_id, layout_id, dynamic_offsets)
            .bound_dynamic_offsets.contains_key(set_index),
        bind_descriptor_set(state, set_index, set_id, layout_id, dynamic_offsets)
            .bound_dynamic_offsets[set_index] == dynamic_offsets,
{
}

/// Binding a descriptor set at one index preserves bindings at other indices.
pub proof fn lemma_bind_preserves_other_sets(
    state: RecordingState,
    set_index: nat,
    set_id: nat,
    layout_id: nat,
    dynamic_offsets: Seq<nat>,
    other_index: nat,
)
    requires
        other_index != set_index,
        state.bound_descriptor_sets.contains_key(other_index),
    ensures
        bind_descriptor_set(state, set_index, set_id, layout_id, dynamic_offsets)
            .bound_descriptor_sets.contains_key(other_index),
        bind_descriptor_set(state, set_index, set_id, layout_id, dynamic_offsets)
            .bound_descriptor_sets[other_index]
            == state.bound_descriptor_sets[other_index],
{
}

/// bound_set_layouts is consistent with actual descriptor set layout IDs.
pub open spec fn bound_layouts_consistent(
    state: RecordingState,
    dsets: Map<nat, DescriptorSetState>,
) -> bool {
    forall|idx: nat| #![trigger state.bound_descriptor_sets.contains_key(idx)]
        state.bound_descriptor_sets.contains_key(idx)
        && dsets.contains_key(state.bound_descriptor_sets[idx])
        ==> state.bound_set_layouts.contains_key(idx)
            && state.bound_set_layouts[idx] == dsets[state.bound_descriptor_sets[idx]].layout_id
}

/// If all_descriptor_sets_valid holds and bound_set_layouts is consistent with the
/// actual descriptor set layout IDs, then descriptor_sets_bound_for_pipeline holds.
pub proof fn lemma_valid_sets_implies_bound_for_pipeline(
    state: RecordingState,
    pipeline: GraphicsPipelineState,
    dsets: Map<nat, DescriptorSetState>,
    layouts: Map<nat, DescriptorSetLayoutState>,
)
    requires
        all_descriptor_sets_valid(state, pipeline, dsets, layouts),
        bound_layouts_consistent(state, dsets),
    ensures descriptor_sets_bound_for_pipeline(state, pipeline.descriptor_set_layouts),
{
    assert forall|i: int| 0 <= i < pipeline.descriptor_set_layouts.len()
        implies (
            #[trigger] state.bound_descriptor_sets.contains_key(i as nat)
            && state.bound_set_layouts.contains_key(i as nat)
            && state.bound_set_layouts[i as nat] == pipeline.descriptor_set_layouts[i]
        ) by {
        // Trigger all_descriptor_sets_valid
        let _ = pipeline.descriptor_set_layouts[i];
        // This gives us: bound_descriptor_sets.contains_key(i as nat)
        //   && dsets[bound_descriptor_sets[i as nat]].layout_id == pipeline_layouts[i]
        // bound_layouts_consistent triggers on bound_descriptor_sets.contains_key(i as nat)
        // giving us: bound_set_layouts[i as nat] == dsets[bound_descriptor_sets[i as nat]].layout_id
        // Chain: bound_set_layouts[i as nat] == pipeline_layouts[i]
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
/// (For a pipeline with N layouts, binding sets at indices 0..N-1 with matching layouts suffices.)
pub proof fn lemma_sequential_binds_satisfy_pipeline(
    state: RecordingState,
    pipeline_layouts: Seq<nat>,
)
    requires
        pipeline_layouts.len() == 0
        || (forall|i: int| 0 <= i < pipeline_layouts.len() ==> (
            #[trigger] state.bound_descriptor_sets.contains_key(i as nat)
            && state.bound_set_layouts.contains_key(i as nat)
            && state.bound_set_layouts[i as nat] == pipeline_layouts[i]
        )),
    ensures
        descriptor_sets_bound_for_pipeline(state, pipeline_layouts),
{
}

// ── Phase 1: Descriptor Resource Liveness ────────────────────────────

/// Whether a single descriptor binding's resource is alive.
/// Empty bindings are trivially alive. BoundBuffer checks buffer alive,
/// BoundImage checks image alive.
pub open spec fn descriptor_binding_resource_alive(
    binding: DescriptorBinding,
    buffers: Map<nat, BufferState>,
    images: Map<nat, ImageState>,
) -> bool {
    match binding {
        DescriptorBinding::Empty => true,
        DescriptorBinding::BoundBuffer { buffer_id, offset: _, range: _ } =>
            buffers.contains_key(buffer_id) && buffers[buffer_id].alive,
        DescriptorBinding::BoundImage { image_id, layout: _ } =>
            images.contains_key(image_id) && images[image_id].alive,
    }
}

/// All resources referenced by bindings in a descriptor set are alive.
pub open spec fn all_descriptor_resources_alive(
    dset: DescriptorSetState,
    layout: DescriptorSetLayoutState,
    buffers: Map<nat, BufferState>,
    images: Map<nat, ImageState>,
) -> bool {
    forall|i: int| #![trigger layout.bindings[i]]
        0 <= i < layout.bindings.len() ==> {
            let b = layout.bindings[i].binding;
            dset.bindings.contains_key(b)
            ==> descriptor_binding_resource_alive(dset.bindings[b], buffers, images)
        }
}

/// All descriptor sets bound by a pipeline have live resources.
pub open spec fn all_pipeline_descriptor_resources_alive(
    state: RecordingState,
    pipeline: GraphicsPipelineState,
    dsets: Map<nat, DescriptorSetState>,
    layouts: Map<nat, DescriptorSetLayoutState>,
    buffers: Map<nat, BufferState>,
    images: Map<nat, ImageState>,
) -> bool {
    forall|i: int| #![trigger pipeline.descriptor_set_layouts[i]]
        0 <= i < pipeline.descriptor_set_layouts.len() ==> {
            let layout_id = pipeline.descriptor_set_layouts[i];
            state.bound_descriptor_sets.contains_key(i as nat)
            && dsets.contains_key(state.bound_descriptor_sets[i as nat])
            && layouts.contains_key(layout_id)
            ==> all_descriptor_resources_alive(
                dsets[state.bound_descriptor_sets[i as nat]],
                layouts[layout_id],
                buffers,
                images,
            )
        }
}

/// An Empty binding has no resource to check — trivially alive.
pub proof fn lemma_empty_binding_trivially_alive(
    buffers: Map<nat, BufferState>,
    images: Map<nat, ImageState>,
)
    ensures descriptor_binding_resource_alive(
        DescriptorBinding::Empty, buffers, images,
    ),
{
}

/// A BoundBuffer binding passes liveness if the buffer is alive.
pub proof fn lemma_alive_buffer_satisfies_liveness(
    buffer_id: nat, offset: nat, range: nat,
    buffers: Map<nat, BufferState>,
    images: Map<nat, ImageState>,
)
    requires
        buffers.contains_key(buffer_id),
        buffers[buffer_id].alive,
    ensures descriptor_binding_resource_alive(
        DescriptorBinding::BoundBuffer { buffer_id, offset, range },
        buffers, images,
    ),
{
}

/// A BoundImage binding passes liveness if the image is alive.
pub proof fn lemma_alive_image_satisfies_liveness(
    image_id: nat, layout: ImageLayout,
    buffers: Map<nat, BufferState>,
    images: Map<nat, ImageState>,
)
    requires
        images.contains_key(image_id),
        images[image_id].alive,
    ensures descriptor_binding_resource_alive(
        DescriptorBinding::BoundImage { image_id, layout },
        buffers, images,
    ),
{
}

// ── Phase 2: Descriptor Usage Validation ─────────────────────────────

/// The required buffer usage flag for a given descriptor type.
pub open spec fn required_buffer_usage(desc_type: DescriptorType) -> nat {
    match desc_type {
        DescriptorType::UniformBuffer => USAGE_UNIFORM_BUFFER(),
        DescriptorType::UniformBufferDynamic => USAGE_UNIFORM_BUFFER(),
        DescriptorType::StorageBuffer => USAGE_STORAGE_BUFFER(),
        DescriptorType::StorageBufferDynamic => USAGE_STORAGE_BUFFER(),
        _ => 0,  // non-buffer types — no buffer usage required
    }
}

/// The required image usage flag for a given descriptor type.
pub open spec fn required_image_usage(desc_type: DescriptorType) -> nat {
    match desc_type {
        DescriptorType::SampledImage => USAGE_SAMPLED(),
        DescriptorType::CombinedImageSampler => USAGE_SAMPLED(),
        DescriptorType::StorageImage => USAGE_STORAGE_IMAGE(),
        DescriptorType::InputAttachment => USAGE_INPUT_ATTACHMENT(),
        _ => 0,  // non-image types — no image usage required
    }
}

/// A descriptor binding's resource has the correct usage flag for the descriptor type.
pub open spec fn descriptor_binding_usage_valid(
    binding: DescriptorBinding,
    desc_type: DescriptorType,
    buffers: Map<nat, BufferState>,
    images: Map<nat, ImageState>,
) -> bool {
    match binding {
        DescriptorBinding::Empty => true,
        DescriptorBinding::BoundBuffer { buffer_id, offset: _, range: _ } =>
            buffers.contains_key(buffer_id)
            ==> buffers[buffer_id].usage.contains(required_buffer_usage(desc_type)),
        DescriptorBinding::BoundImage { image_id, layout: _ } =>
            images.contains_key(image_id)
            ==> images[image_id].usage.contains(required_image_usage(desc_type)),
    }
}

/// A uniform/storage buffer descriptor requires the matching buffer usage flag.
pub proof fn lemma_buffer_descriptor_needs_usage(
    buffer_id: nat, offset: nat, range: nat,
    desc_type: DescriptorType,
    buffers: Map<nat, BufferState>,
    images: Map<nat, ImageState>,
)
    requires
        buffers.contains_key(buffer_id),
        buffers[buffer_id].usage.contains(required_buffer_usage(desc_type)),
    ensures descriptor_binding_usage_valid(
        DescriptorBinding::BoundBuffer { buffer_id, offset, range },
        desc_type, buffers, images,
    ),
{
}

/// A sampled/storage/input image descriptor requires the matching image usage flag.
pub proof fn lemma_image_descriptor_needs_usage(
    image_id: nat, layout: ImageLayout,
    desc_type: DescriptorType,
    buffers: Map<nat, BufferState>,
    images: Map<nat, ImageState>,
)
    requires
        images.contains_key(image_id),
        images[image_id].usage.contains(required_image_usage(desc_type)),
    ensures descriptor_binding_usage_valid(
        DescriptorBinding::BoundImage { image_id, layout },
        desc_type, buffers, images,
    ),
{
}

// ── Phase 5: Descriptor Update Synchronization ───────────────────────

/// A descriptor set is safe to update if the thread holds exclusive access.
pub open spec fn descriptor_set_safe_to_update(
    set_id: nat,
    thread: ThreadId,
    reg: TokenRegistry,
) -> bool {
    holds_exclusive(reg, set_id, thread)
}

/// A descriptor set is not referenced by any in-flight (uncompleted) submission.
pub open spec fn descriptor_set_not_in_flight(
    set_id: nat,
    pending: Seq<SubmissionRecord>,
) -> bool {
    forall|i: int| 0 <= i < pending.len() ==>
        (#[trigger] pending[i]).completed
        || !pending[i].referenced_resources.contains(ResourceId::DescriptorSet { id: set_id })
}

/// A descriptor set update is safe: exclusive access AND not in flight.
pub open spec fn update_descriptor_safe(
    set_id: nat,
    thread: ThreadId,
    reg: TokenRegistry,
    pending: Seq<SubmissionRecord>,
) -> bool {
    descriptor_set_safe_to_update(set_id, thread, reg)
    && descriptor_set_not_in_flight(set_id, pending)
}

/// Exclusive access + not in flight → safe to update.
pub proof fn lemma_exclusive_access_enables_update(
    set_id: nat,
    thread: ThreadId,
    reg: TokenRegistry,
    pending: Seq<SubmissionRecord>,
)
    requires
        holds_exclusive(reg, set_id, thread),
        descriptor_set_not_in_flight(set_id, pending),
    ensures update_descriptor_safe(set_id, thread, reg, pending),
{
}

/// After vkDeviceWaitIdle (all submissions completed), any set is safe to update
/// given exclusive access.
pub proof fn lemma_idle_device_safe_to_update(
    set_id: nat,
    thread: ThreadId,
    reg: TokenRegistry,
    pending: Seq<SubmissionRecord>,
)
    requires
        holds_exclusive(reg, set_id, thread),
        forall|i: int| 0 <= i < pending.len() ==> (#[trigger] pending[i]).completed,
    ensures update_descriptor_safe(set_id, thread, reg, pending),
{
}

/// Completed submissions don't block descriptor set updates.
pub proof fn lemma_completed_submission_frees_set(
    set_id: nat,
    pending: Seq<SubmissionRecord>,
)
    requires
        forall|i: int| 0 <= i < pending.len() ==> (#[trigger] pending[i]).completed,
    ensures descriptor_set_not_in_flight(set_id, pending),
{
}

} // verus!
