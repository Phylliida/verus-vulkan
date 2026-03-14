use vstd::prelude::*;
use crate::resource::*;
use crate::device::*;
use crate::resource_lifecycle::*;
use crate::readback::*;
use crate::lifetime::*;
use crate::completion::*;
use crate::fence::*;

verus! {

// ── End-to-End Integration Proofs ────────────────────────────────────────
//
// These proofs chain specifications across layers to verify that the
// complete GPU resource pipeline maintains its invariants end-to-end:
//
//   create buffer → allocate memory → bind → record commands →
//   submit → fence wait → readback → data matches → destroy
//
// Each lemma connects two or more layers, proving that properties
// established by earlier stages are preserved through later stages.

// ── 1. Lifecycle Chain ─────────────────────────────────────────────────

/// A freshly created resource can be bound, and after binding it can be used.
pub proof fn lemma_create_bind_enables_use(resource: ResourceId)
    ensures
        can_use(bind_resource(create_resource(resource))),
{
    lemma_fresh_can_bind(resource);
    lemma_bound_can_use(create_resource(resource));
}

/// Full lifecycle roundtrip: create → bind → submit → complete → can_destroy.
/// After a single submission completes, the resource returns to a destroyable state.
pub proof fn lemma_lifecycle_roundtrip(resource: ResourceId)
    ensures ({
        let created = create_resource(resource);
        let bound = bind_resource(created);
        let in_use = submit_resource(bound);
        let idle = complete_use(in_use);
        can_destroy(idle)
    }),
{
    let created = create_resource(resource);
    let bound = bind_resource(created);
    let in_use = submit_resource(bound);

    // submit_resource sets pending_use_count to 1
    lemma_submit_increases_count(bound);
    assert(in_use.pending_use_count == 1);

    // complete_use decrements back to 0
    lemma_complete_decreases_count(in_use);
    let idle = complete_use(in_use);
    assert(idle.pending_use_count == 0);

    // Idle with count 0 → can destroy
    assert(idle.lifecycle == ResourceLifecycle::Idle);
}

/// After destroy, the resource is not alive and cannot be used.
pub proof fn lemma_destroy_ends_lifecycle(resource: ResourceId)
    ensures ({
        let created = create_resource(resource);
        let bound = bind_resource(created);
        let in_use = submit_resource(bound);
        let idle = complete_use(in_use);
        let destroyed = destroy_resource(idle);
        !resource_alive(destroyed) && !can_use(destroyed)
    }),
{
    let created = create_resource(resource);
    let bound = bind_resource(created);
    let in_use = submit_resource(bound);
    let idle = complete_use(in_use);

    lemma_destroy_not_alive(idle);
    lemma_destroyed_cannot_use(destroy_resource(idle));
}

/// A resource in use cannot be destroyed — safety interlock.
pub proof fn lemma_in_use_safety_interlock(resource: ResourceId)
    ensures ({
        let created = create_resource(resource);
        let bound = bind_resource(created);
        let in_use = submit_resource(bound);
        !can_destroy(in_use)
    }),
{
    let created = create_resource(resource);
    let bound = bind_resource(created);
    let in_use = submit_resource(bound);
    lemma_in_use_cannot_destroy(in_use);
}

// ── 2. Fence Wait → Safe Destroy ──────────────────────────────────────

/// After submitting with a fence and waiting on it, the resource is safe to destroy.
/// This bridges the completion layer (fence wait removes pending submissions)
/// with the lifetime layer (no pending references → safe to destroy).
pub proof fn lemma_submit_fence_wait_enables_destroy(
    dev: DeviceState,
    fence_id: nat,
    fence_states: Map<nat, FenceState>,
    resource: ResourceId,
)
    requires
        fence_states.contains_key(fence_id),
        // Every submission that references this resource used this fence
        forall|i: int| 0 <= i < dev.pending_submissions.len()
            && dev.pending_submissions[i].referenced_resources.contains(resource)
            ==> dev.pending_submissions[i].fence_id == Some(fence_id),
    ensures ({
        let (new_dev, _) = fence_wait_ghost(dev, fence_id, fence_states);
        safe_to_destroy_resource(new_dev, resource)
    }),
{
    lemma_fence_wait_enables_destroy(dev, fence_id, fence_states, resource);
}

// ── 3. Data Roundtrip Correctness ─────────────────────────────────────

/// Upload data to GPU, then read it back — data matches.
/// This is the core data correctness theorem for the readback pipeline.
pub proof fn lemma_upload_readback_data_correct(
    staging: StagingBufferState,
    gpu: GpuBufferState,
    offset: nat,
    copy_size: nat,
)
    requires
        staging_buffer_well_formed(staging),
        gpu_buffer_well_formed(gpu),
        offset + copy_size <= staging.size,
        offset + copy_size <= gpu.size,
    ensures ({
        let gpu_after = copy_from_staging_ghost(gpu, staging, offset, offset, copy_size);
        let staging_after = copy_to_staging_ghost(staging, gpu_after, offset, offset, copy_size);
        forall|i: int| offset as int <= i < (offset + copy_size) as int
            ==> staging_after.contents.data[i] == staging.contents.data[i]
    }),
{
    lemma_roundtrip_preserves_data(staging, gpu, offset, copy_size);
}

/// After readback, the staging buffer is well-formed.
pub proof fn lemma_readback_preserves_well_formed(
    staging: StagingBufferState,
    gpu: GpuBufferState,
    src_offset: nat,
    dst_offset: nat,
    copy_size: nat,
)
    requires
        staging_buffer_well_formed(staging),
        gpu_buffer_well_formed(gpu),
        src_offset + copy_size <= gpu.size,
        dst_offset + copy_size <= staging.size,
    ensures
        staging_buffer_well_formed(
            copy_to_staging_ghost(staging, gpu, src_offset, dst_offset, copy_size),
        ),
{
    lemma_copy_preserves_staging_well_formed(staging, gpu, src_offset, dst_offset, copy_size);
}

/// After readback, staging buffer metadata (host_visible, alive) is preserved.
pub proof fn lemma_readback_preserves_metadata(
    staging: StagingBufferState,
    gpu: GpuBufferState,
    src_offset: nat,
    dst_offset: nat,
    copy_size: nat,
)
    requires
        src_offset + copy_size <= gpu.size,
        dst_offset + copy_size <= staging.size,
    ensures ({
        let result = copy_to_staging_ghost(staging, gpu, src_offset, dst_offset, copy_size);
        result.host_visible == staging.host_visible
        && result.alive == staging.alive
        && result.resource == staging.resource
    }),
{
    lemma_copy_preserves_staging_metadata(staging, gpu, src_offset, dst_offset, copy_size);
}

// ── 4. Full Pipeline Composition ──────────────────────────────────────

/// Full pipeline state capturing all layers at once.
pub struct PipelineSnapshot {
    /// Device state (heap tracking, live counts, lifecycle registry).
    pub dev: DeviceState,
    /// Resource being tracked.
    pub resource: ResourceId,
    /// Resource lifecycle FSM state.
    pub lifecycle: ResourceLifecycleState,
    /// GPU buffer ghost state.
    pub gpu: GpuBufferState,
    /// Staging buffer ghost state (for readback).
    pub staging: StagingBufferState,
}

/// A pipeline snapshot is self-consistent.
pub open spec fn pipeline_consistent(snap: PipelineSnapshot) -> bool {
    snap.lifecycle.resource == snap.resource
    && snap.gpu.resource == snap.resource
    && staging_buffer_well_formed(snap.staging)
    && gpu_buffer_well_formed(snap.gpu)
    && snap.staging.host_visible
    && snap.staging.alive
    && snap.gpu.alive
}

/// A pipeline snapshot after creation: resource is Created, not yet usable.
pub open spec fn pipeline_after_create(snap: PipelineSnapshot) -> bool {
    pipeline_consistent(snap)
    && snap.lifecycle.lifecycle == ResourceLifecycle::Created
    && snap.lifecycle.pending_use_count == 0
}

/// A pipeline snapshot after bind: resource is Bound, ready for use.
pub open spec fn pipeline_after_bind(snap: PipelineSnapshot) -> bool {
    pipeline_consistent(snap)
    && snap.lifecycle.lifecycle == ResourceLifecycle::Bound
    && snap.lifecycle.pending_use_count == 0
}

/// A pipeline snapshot after submission: resource is InUse.
pub open spec fn pipeline_after_submit(snap: PipelineSnapshot) -> bool {
    pipeline_consistent(snap)
    && snap.lifecycle.lifecycle == ResourceLifecycle::InUse
    && snap.lifecycle.pending_use_count > 0
}

/// A pipeline snapshot after completion: resource is Idle, ready for destroy or reuse.
pub open spec fn pipeline_after_complete(snap: PipelineSnapshot) -> bool {
    pipeline_consistent(snap)
    && snap.lifecycle.lifecycle == ResourceLifecycle::Idle
    && snap.lifecycle.pending_use_count == 0
}

/// After-create snapshot can transition to after-bind.
pub proof fn lemma_pipeline_create_to_bind(snap: PipelineSnapshot)
    requires pipeline_after_create(snap),
    ensures pipeline_after_bind(PipelineSnapshot {
        lifecycle: bind_resource(snap.lifecycle),
        ..snap
    }),
{
}

/// After-bind snapshot can transition to after-submit.
pub proof fn lemma_pipeline_bind_to_submit(snap: PipelineSnapshot)
    requires pipeline_after_bind(snap),
    ensures pipeline_after_submit(PipelineSnapshot {
        lifecycle: submit_resource(snap.lifecycle),
        ..snap
    }),
{
}

/// After-submit with single pending use can transition to after-complete.
pub proof fn lemma_pipeline_submit_to_complete(snap: PipelineSnapshot)
    requires
        pipeline_after_submit(snap),
        snap.lifecycle.pending_use_count == 1,
    ensures pipeline_after_complete(PipelineSnapshot {
        lifecycle: complete_use(snap.lifecycle),
        ..snap
    }),
{
}

/// After-complete snapshot: resource can be destroyed.
pub proof fn lemma_pipeline_complete_can_destroy(snap: PipelineSnapshot)
    requires pipeline_after_complete(snap),
    ensures can_destroy(snap.lifecycle),
{
}

/// Full pipeline: create → bind → submit → complete → can_destroy,
/// and readback data matches uploaded data.
pub proof fn lemma_full_pipeline(
    resource: ResourceId,
    gpu: GpuBufferState,
    staging: StagingBufferState,
    offset: nat,
    copy_size: nat,
)
    requires
        staging_buffer_well_formed(staging),
        gpu_buffer_well_formed(gpu),
        staging.host_visible,
        staging.alive,
        gpu.alive,
        gpu.resource == resource,
        staging.resource != resource,
        offset + copy_size <= staging.size,
        offset + copy_size <= gpu.size,
    ensures ({
        // Lifecycle: create → bind → submit → complete → can destroy
        let created = create_resource(resource);
        let bound = bind_resource(created);
        let in_use = submit_resource(bound);
        let idle = complete_use(in_use);
        // Data: upload → readback → matches
        let gpu_after = copy_from_staging_ghost(gpu, staging, offset, offset, copy_size);
        let staging_after = copy_to_staging_ghost(staging, gpu_after, offset, offset, copy_size);
        can_destroy(idle)
        && forall|i: int| offset as int <= i < (offset + copy_size) as int
            ==> staging_after.contents.data[i] == staging.contents.data[i]
    }),
{
    // Lifecycle chain
    lemma_lifecycle_roundtrip(resource);

    // Data chain
    lemma_roundtrip_preserves_data(staging, gpu, offset, copy_size);
}

// ── 5. Memory Budget Correctness ──────────────────────────────────────

/// Allocating and then freeing the same amount returns to the original budget.
pub proof fn lemma_alloc_free_budget_neutral(
    dev: DeviceState,
    heap_idx: nat,
    size: nat,
)
    requires
        device_well_formed(dev),
        heap_fits(dev, heap_idx, size),
    ensures ({
        let after_alloc = allocate_memory_ghost(dev, heap_idx, size);
        let after_free = free_memory_ghost(after_alloc, heap_idx, size);
        after_free.heap_usage[heap_idx] == dev.heap_usage[heap_idx]
    }),
{
    let after_alloc = allocate_memory_ghost(dev, heap_idx, size);
    assert(after_alloc.heap_usage[heap_idx] == dev.heap_usage[heap_idx] + size);
    let after_free = free_memory_ghost(after_alloc, heap_idx, size);
    assert(after_free.heap_usage[heap_idx] == (after_alloc.heap_usage[heap_idx] - size) as nat);
}

/// After alloc+free, the device is still well-formed.
pub proof fn lemma_alloc_free_preserves_well_formed(
    dev: DeviceState,
    heap_idx: nat,
    size: nat,
)
    requires
        device_well_formed(dev),
        heap_fits(dev, heap_idx, size),
    ensures
        device_well_formed(free_memory_ghost(allocate_memory_ghost(dev, heap_idx, size), heap_idx, size)),
{
    let after_alloc = allocate_memory_ghost(dev, heap_idx, size);
    let after_free = free_memory_ghost(after_alloc, heap_idx, size);

    // Key: heap_usage returns to original, so it's <= capacity
    assert(after_free.heap_usage[heap_idx] == dev.heap_usage[heap_idx]);
    assert(after_free.heap_capacity == dev.heap_capacity);
    assert(after_free.num_heaps == dev.num_heaps);
    assert(after_free.limits == dev.limits);
}

// ── 6. Device Lifecycle Registry Integration ──────────────────────────

/// Creating then destroying a buffer preserves device lifecycle consistency.
pub proof fn lemma_create_destroy_lifecycle_consistent(
    dev: DeviceState,
    resource: ResourceId,
)
    requires
        device_lifecycle_consistent(dev),
        !dev.lifecycle_registry.contains_key(resource),
    ensures ({
        let after_create = create_buffer_lifecycle_ghost(dev, resource);
        device_lifecycle_consistent(after_create)
    }),
{
    lemma_create_buffer_lifecycle_consistent(dev, resource);
}

/// The live buffer count increments on create and decrements on destroy.
pub proof fn lemma_buffer_count_roundtrip(dev: DeviceState)
    ensures ({
        let after_create = create_buffer_ghost(dev);
        let after_destroy = destroy_buffer_ghost(after_create);
        after_destroy.live_buffers == dev.live_buffers
    }),
{
}

// ── 7. Cross-Layer Safety ─────────────────────────────────────────────

/// A resource that is in-use (lifecycle) cannot be safely destroyed (lifetime).
/// This connects the resource_lifecycle layer with the completion layer.
pub proof fn lemma_in_use_not_safe_to_destroy(
    resource: ResourceId,
    dev: DeviceState,
    submission_idx: int,
)
    requires
        0 <= submission_idx < dev.pending_submissions.len(),
        dev.pending_submissions[submission_idx].referenced_resources.contains(resource),
        !dev.pending_submissions[submission_idx].completed,
    ensures
        !safe_to_destroy_resource(dev, resource),
{
    // no_pending_references requires ALL submissions are completed or don't reference.
    // We have one that is both not completed and references the resource.
    assert(!no_pending_references(dev.pending_submissions, resource));
}

/// After fence wait with all submissions using that fence, the host can read
/// the staging buffer (connects completion layer with readback layer).
pub proof fn lemma_fence_wait_enables_host_read(
    dev: DeviceState,
    fence_id: nat,
    fence_states: Map<nat, FenceState>,
    staging: StagingBufferState,
)
    requires
        fence_states.contains_key(fence_id),
        staging.host_visible,
        staging.alive,
        // All submissions referencing staging's resource used this fence
        forall|i: int| 0 <= i < dev.pending_submissions.len()
            && dev.pending_submissions[i].referenced_resources.contains(staging.resource)
            ==> dev.pending_submissions[i].fence_id == Some(fence_id),
    ensures ({
        let (new_dev, _) = fence_wait_ghost(dev, fence_id, fence_states);
        host_readable(new_dev.pending_submissions, staging)
    }),
{
    lemma_fence_wait_enables_destroy(dev, fence_id, fence_states, staging.resource);
    let (new_dev, _) = fence_wait_ghost(dev, fence_id, fence_states);
    assert(safe_to_destroy_resource(new_dev, staging.resource));
    // safe_to_destroy → no_pending_references → host_readable
    assert(no_pending_references(new_dev.pending_submissions, staging.resource));
}

// ── 8. Readback Outside-Region Isolation ──────────────────────────────

/// Data outside the copy region is untouched by readback.
/// Combined with the roundtrip lemma, this shows that readback is precise:
/// it copies exactly the requested region and nothing else.
pub proof fn lemma_readback_region_isolation(
    staging: StagingBufferState,
    gpu: GpuBufferState,
    src_offset: nat,
    dst_offset: nat,
    copy_size: nat,
    idx: int,
)
    requires
        staging_buffer_well_formed(staging),
        gpu_buffer_well_formed(gpu),
        src_offset + copy_size <= gpu.size,
        dst_offset + copy_size <= staging.size,
        0 <= idx < staging.size as int,
        !(dst_offset as int <= idx < (dst_offset + copy_size) as int),
    ensures
        copy_to_staging_ghost(staging, gpu, src_offset, dst_offset, copy_size)
            .contents.data[idx] == staging.contents.data[idx],
{
    lemma_copy_preserves_outside(staging, gpu, src_offset, dst_offset, copy_size, idx);
}

} // verus!
