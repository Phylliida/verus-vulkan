use vstd::prelude::*;
use crate::resource::*;
use crate::lifetime::*;
use crate::format_properties::*;

verus! {

/// Device hardware limits relevant to validation.
pub struct DeviceLimits {
    /// Minimum alignment (in bytes) for uniform buffer descriptor offsets.
    pub min_uniform_buffer_offset_alignment: nat,
    /// Minimum alignment (in bytes) for storage buffer descriptor offsets.
    pub min_storage_buffer_offset_alignment: nat,
    /// Minimum alignment (in bytes) for texel buffer descriptor offsets.
    pub min_texel_buffer_offset_alignment: nat,
    /// Maximum total size (in bytes) of push constant ranges.
    pub max_push_constants_size: nat,
}

/// Ghost state for the Vulkan logical device.
///
/// Tracks heap budgets, resource counters, and pending GPU submissions.
/// All fields are ghost-level (nat/Map) — the exec layer will map
/// runtime handles to these ghost IDs.
pub struct DeviceState {
    /// Current usage (in bytes) of each memory heap.
    pub heap_usage: Map<nat, nat>,
    /// Maximum capacity (in bytes) of each memory heap.
    pub heap_capacity: Map<nat, nat>,
    /// Number of memory heaps on this device.
    pub num_heaps: nat,
    /// Maps memory type index → heap index.
    pub memory_type_to_heap: Map<nat, nat>,
    /// Number of memory types exposed by the device.
    pub num_memory_types: nat,
    /// Log of pending GPU submissions (not yet completed or retired).
    pub pending_submissions: Seq<SubmissionRecord>,
    /// Count of live (not destroyed) buffers.
    pub live_buffers: nat,
    /// Count of live images.
    pub live_images: nat,
    /// Count of live pipelines.
    pub live_pipelines: nat,
    /// Count of live descriptor pools.
    pub live_descriptor_pools: nat,
    /// Hardware limits for alignment and size validation.
    pub limits: DeviceLimits,
    /// Per-format feature properties, keyed by format ID.
    pub format_properties: Map<nat, FormatProperties>,
}

/// The device state is well-formed if:
/// - All heaps have defined usage and capacity with usage <= capacity.
/// - All memory types map to valid heap indices.
pub open spec fn device_well_formed(dev: DeviceState) -> bool {
    &&& (forall|h: nat| #![trigger dev.heap_usage.contains_key(h)]
        h < dev.num_heaps ==>
        dev.heap_usage.contains_key(h)
        && dev.heap_capacity.contains_key(h)
        && dev.heap_usage[h] <= dev.heap_capacity[h])
    &&& (forall|mt: nat| #![trigger dev.memory_type_to_heap.contains_key(mt)]
        mt < dev.num_memory_types ==>
        dev.memory_type_to_heap.contains_key(mt)
        && dev.memory_type_to_heap[mt] < dev.num_heaps)
    &&& dev.limits.min_uniform_buffer_offset_alignment > 0
    &&& dev.limits.min_storage_buffer_offset_alignment > 0
    &&& dev.limits.min_texel_buffer_offset_alignment > 0
}

/// Whether the device has format properties registered for a given format ID.
pub open spec fn device_has_format(dev: DeviceState, format_id: nat) -> bool {
    dev.format_properties.contains_key(format_id)
}

/// Get the format properties for a given format ID.
pub open spec fn device_format_props(dev: DeviceState, format_id: nat) -> FormatProperties
    recommends dev.format_properties.contains_key(format_id),
{
    dev.format_properties[format_id]
}

/// True iff allocating `size` bytes on `heap_idx` would stay within budget.
pub open spec fn heap_fits(dev: DeviceState, heap_idx: nat, size: nat) -> bool {
    heap_idx < dev.num_heaps
    && dev.heap_usage.contains_key(heap_idx)
    && dev.heap_capacity.contains_key(heap_idx)
    && dev.heap_usage[heap_idx] + size <= dev.heap_capacity[heap_idx]
}

/// Ghost update: allocate `size` bytes from `heap_idx`.
pub open spec fn allocate_memory_ghost(
    dev: DeviceState,
    heap_idx: nat,
    size: nat,
) -> DeviceState
    recommends heap_fits(dev, heap_idx, size),
{
    DeviceState {
        heap_usage: dev.heap_usage.insert(heap_idx, dev.heap_usage[heap_idx] + size),
        ..dev
    }
}

/// Ghost update: free `size` bytes from `heap_idx`.
pub open spec fn free_memory_ghost(
    dev: DeviceState,
    heap_idx: nat,
    size: nat,
) -> DeviceState
    recommends
        heap_idx < dev.num_heaps,
        dev.heap_usage.contains_key(heap_idx),
        size <= dev.heap_usage[heap_idx],
{
    DeviceState {
        heap_usage: dev.heap_usage.insert(heap_idx, (dev.heap_usage[heap_idx] - size) as nat),
        ..dev
    }
}

/// Ghost update: increment live buffer count.
pub open spec fn create_buffer_ghost(dev: DeviceState) -> DeviceState {
    DeviceState {
        live_buffers: dev.live_buffers + 1,
        ..dev
    }
}

/// Ghost update: decrement live buffer count.
pub open spec fn destroy_buffer_ghost(dev: DeviceState) -> DeviceState
    recommends dev.live_buffers > 0,
{
    DeviceState {
        live_buffers: (dev.live_buffers - 1) as nat,
        ..dev
    }
}

/// Ghost update: increment live image count.
pub open spec fn create_image_ghost(dev: DeviceState) -> DeviceState {
    DeviceState {
        live_images: dev.live_images + 1,
        ..dev
    }
}

/// Ghost update: decrement live image count.
pub open spec fn destroy_image_ghost(dev: DeviceState) -> DeviceState
    recommends dev.live_images > 0,
{
    DeviceState {
        live_images: (dev.live_images - 1) as nat,
        ..dev
    }
}

/// True iff the device has no live resources and no pending submissions.
/// This is the precondition for vkDestroyDevice.
pub open spec fn device_ready_for_shutdown(dev: DeviceState) -> bool {
    dev.live_buffers == 0
    && dev.live_images == 0
    && dev.live_pipelines == 0
    && dev.live_descriptor_pools == 0
    && dev.pending_submissions.len() == 0
}

// ── Wait-Idle Specs ─────────────────────────────────────────────────────

/// Filter out all submissions belonging to a specific queue.
/// Returns only submissions from OTHER queues (removes `queue_id`'s submissions).
pub open spec fn filter_by_queue(
    submissions: Seq<SubmissionRecord>,
    queue_id: nat,
) -> Seq<SubmissionRecord>
    decreases submissions.len(),
{
    if submissions.len() == 0 {
        Seq::empty()
    } else {
        let head = submissions[0];
        let rest = filter_by_queue(submissions.subrange(1, submissions.len() as int), queue_id);
        if head.queue_id == queue_id {
            rest
        } else {
            Seq::new(1, |_i| head).add(rest)
        }
    }
}

/// Ghost update: vkDeviceWaitIdle — all pending submissions complete.
pub open spec fn device_wait_idle_ghost(dev: DeviceState) -> DeviceState {
    DeviceState {
        pending_submissions: Seq::empty(),
        ..dev
    }
}

/// Ghost update: vkQueueWaitIdle — all submissions on `queue_id` complete.
pub open spec fn queue_wait_idle_ghost(
    dev: DeviceState,
    queue_id: nat,
) -> DeviceState {
    DeviceState {
        pending_submissions: filter_by_queue(dev.pending_submissions, queue_id),
        ..dev
    }
}

// ── Lemmas ──────────────────────────────────────────────────────────────

/// After vkDeviceWaitIdle with zero resource counters, the device is ready for shutdown.
pub proof fn lemma_wait_idle_enables_shutdown(dev: DeviceState)
    requires
        dev.live_buffers == 0,
        dev.live_images == 0,
        dev.live_pipelines == 0,
        dev.live_descriptor_pools == 0,
    ensures
        device_ready_for_shutdown(device_wait_idle_ghost(dev)),
{
}

/// vkDeviceWaitIdle preserves device_well_formed (heap fields unchanged).
pub proof fn lemma_wait_idle_preserves_well_formed(dev: DeviceState)
    requires device_well_formed(dev),
    ensures device_well_formed(device_wait_idle_ghost(dev)),
{
}

/// Allocating within budget preserves device_well_formed.
pub proof fn lemma_allocate_preserves_well_formed(
    dev: DeviceState,
    heap_idx: nat,
    size: nat,
)
    requires
        device_well_formed(dev),
        heap_fits(dev, heap_idx, size),
    ensures
        device_well_formed(allocate_memory_ghost(dev, heap_idx, size)),
{
    let new_dev = allocate_memory_ghost(dev, heap_idx, size);
    let new_usage = dev.heap_usage.insert(heap_idx, dev.heap_usage[heap_idx] + size);

    assert forall|h: nat|
        #![trigger new_usage.contains_key(h)]
        h < dev.num_heaps
        implies
        new_usage.contains_key(h)
        && dev.heap_capacity.contains_key(h)
        && new_usage[h] <= dev.heap_capacity[h]
    by {
        assert(dev.heap_usage.contains_key(h));
        if h == heap_idx {
        } else {
            assert(new_usage.contains_key(h));
            assert(new_usage[h] == dev.heap_usage[h]);
        }
    }
}

/// Freeing memory decreases usage and preserves device_well_formed.
pub proof fn lemma_free_restores_budget(
    dev: DeviceState,
    heap_idx: nat,
    size: nat,
)
    requires
        device_well_formed(dev),
        heap_idx < dev.num_heaps,
        size <= dev.heap_usage[heap_idx],
    ensures
        device_well_formed(free_memory_ghost(dev, heap_idx, size)),
        free_memory_ghost(dev, heap_idx, size).heap_usage[heap_idx]
            == dev.heap_usage[heap_idx] - size,
{
    let new_dev = free_memory_ghost(dev, heap_idx, size);
    let new_usage = dev.heap_usage.insert(heap_idx, (dev.heap_usage[heap_idx] - size) as nat);

    assert forall|h: nat|
        #![trigger new_usage.contains_key(h)]
        h < dev.num_heaps
        implies
        new_usage.contains_key(h)
        && dev.heap_capacity.contains_key(h)
        && new_usage[h] <= dev.heap_capacity[h]
    by {
        assert(dev.heap_usage.contains_key(h));
        if h == heap_idx {
        } else {
            assert(new_usage.contains_key(h));
            assert(new_usage[h] == dev.heap_usage[h]);
        }
    }
}

/// Creating a buffer increments live_buffers by 1.
pub proof fn lemma_create_buffer_increments(dev: DeviceState)
    ensures
        create_buffer_ghost(dev).live_buffers == dev.live_buffers + 1,
{
}

/// Destroying a buffer decrements live_buffers by 1.
pub proof fn lemma_destroy_buffer_decrements(dev: DeviceState)
    requires dev.live_buffers > 0,
    ensures
        destroy_buffer_ghost(dev).live_buffers == dev.live_buffers - 1,
{
}

/// A device with zero resource counters and no submissions is ready for shutdown.
pub proof fn lemma_empty_device_ready_for_shutdown(dev: DeviceState)
    requires
        dev.live_buffers == 0,
        dev.live_images == 0,
        dev.live_pipelines == 0,
        dev.live_descriptor_pools == 0,
        dev.pending_submissions.len() == 0,
    ensures
        device_ready_for_shutdown(dev),
{
}

/// Creating a buffer preserves device_well_formed.
pub proof fn lemma_create_buffer_preserves_well_formed(dev: DeviceState)
    requires device_well_formed(dev),
    ensures device_well_formed(create_buffer_ghost(dev)),
{
}

/// Destroying a buffer preserves device_well_formed.
pub proof fn lemma_destroy_buffer_preserves_well_formed(dev: DeviceState)
    requires device_well_formed(dev), dev.live_buffers > 0,
    ensures device_well_formed(destroy_buffer_ghost(dev)),
{
}

/// Creating an image increments live_images by 1.
pub proof fn lemma_create_image_increments(dev: DeviceState)
    ensures create_image_ghost(dev).live_images == dev.live_images + 1,
{
}

/// Destroying an image decrements live_images by 1.
pub proof fn lemma_destroy_image_decrements(dev: DeviceState)
    requires dev.live_images > 0,
    ensures destroy_image_ghost(dev).live_images == dev.live_images - 1,
{
}

/// Creating an image preserves device_well_formed.
pub proof fn lemma_create_image_preserves_well_formed(dev: DeviceState)
    requires device_well_formed(dev),
    ensures device_well_formed(create_image_ghost(dev)),
{
}

/// Queue wait idle preserves device_well_formed.
pub proof fn lemma_queue_wait_idle_preserves_well_formed(
    dev: DeviceState, queue_id: nat,
)
    requires device_well_formed(dev),
    ensures device_well_formed(queue_wait_idle_ghost(dev, queue_id)),
{
    let new_dev = queue_wait_idle_ghost(dev, queue_id);
    assert(new_dev.limits == dev.limits);
}

} // verus!
