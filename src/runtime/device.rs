use vstd::prelude::*;
use crate::device::*;
use crate::memory::*;
use crate::lifetime::*;

verus! {

/// Runtime wrapper for a Vulkan logical device.
pub struct RuntimeDevice {
    /// Opaque handle (maps to VkDevice).
    pub handle: u64,
    /// Ghost model of the device state.
    pub state: Ghost<DeviceState>,
}

impl View for RuntimeDevice {
    type V = DeviceState;
    open spec fn view(&self) -> DeviceState { self.state@ }
}

/// Well-formedness of the runtime device.
pub open spec fn runtime_device_wf(dev: &RuntimeDevice) -> bool {
    device_well_formed(dev@)
}

/// Ghost-level create device: returns a well-formed initial state.
pub open spec fn create_device_spec(
    num_heaps: nat,
    heap_caps: Map<nat, nat>,
    num_memory_types: nat,
    mt_to_heap: Map<nat, nat>,
) -> DeviceState {
    DeviceState {
        heap_usage: Map::new(
            |h: nat| h < num_heaps,
            |h: nat| 0nat,
        ),
        heap_capacity: heap_caps,
        num_heaps: num_heaps,
        memory_type_to_heap: mt_to_heap,
        num_memory_types: num_memory_types,
        pending_submissions: Seq::empty(),
        live_buffers: 0,
        live_images: 0,
        live_pipelines: 0,
        live_descriptor_pools: 0,
    }
}

/// Exec: create a buffer (increments live_buffers in ghost state).
pub fn create_buffer_exec(dev: &mut RuntimeDevice)
    requires
        runtime_device_wf(&*old(dev)),
    ensures
        dev@ == create_buffer_ghost(old(dev)@),
{
    dev.state = Ghost(create_buffer_ghost(dev.state@));
}

/// Exec: destroy a buffer (decrements live_buffers in ghost state).
pub fn destroy_buffer_exec(dev: &mut RuntimeDevice)
    requires
        runtime_device_wf(&*old(dev)),
        old(dev)@.live_buffers > 0,
    ensures
        dev@ == destroy_buffer_ghost(old(dev)@),
{
    dev.state = Ghost(destroy_buffer_ghost(dev.state@));
}

/// Exec: create an image (increments live_images in ghost state).
pub fn create_image_exec(dev: &mut RuntimeDevice)
    requires
        runtime_device_wf(&*old(dev)),
    ensures
        dev@ == create_image_ghost(old(dev)@),
{
    dev.state = Ghost(create_image_ghost(dev.state@));
}

/// Exec: destroy an image (decrements live_images in ghost state).
pub fn destroy_image_exec(dev: &mut RuntimeDevice)
    requires
        runtime_device_wf(&*old(dev)),
        old(dev)@.live_images > 0,
    ensures
        dev@ == destroy_image_ghost(old(dev)@),
{
    dev.state = Ghost(destroy_image_ghost(dev.state@));
}

/// Exec: allocate memory on a specific heap.
pub fn allocate_memory_exec(dev: &mut RuntimeDevice, heap_idx: u64, size: u64)
    requires
        runtime_device_wf(&*old(dev)),
        heap_fits(old(dev)@, heap_idx as nat, size as nat),
    ensures
        dev@ == allocate_memory_ghost(old(dev)@, heap_idx as nat, size as nat),
{
    dev.state = Ghost(allocate_memory_ghost(dev.state@, heap_idx as nat, size as nat));
}

/// Exec: free memory on a specific heap.
pub fn free_memory_exec(dev: &mut RuntimeDevice, heap_idx: u64, size: u64)
    requires
        runtime_device_wf(&*old(dev)),
        (heap_idx as nat) < old(dev)@.num_heaps,
        old(dev)@.heap_usage.contains_key(heap_idx as nat),
        size as nat <= old(dev)@.heap_usage[heap_idx as nat],
    ensures
        dev@ == free_memory_ghost(old(dev)@, heap_idx as nat, size as nat),
{
    dev.state = Ghost(free_memory_ghost(dev.state@, heap_idx as nat, size as nat));
}

/// Exec: device wait idle — all pending submissions complete.
pub fn device_wait_idle_exec(dev: &mut RuntimeDevice)
    requires
        runtime_device_wf(&*old(dev)),
    ensures
        dev@ == device_wait_idle_ghost(old(dev)@),
{
    dev.state = Ghost(device_wait_idle_ghost(dev.state@));
}

// ── Extended Specs & Proofs ──────────────────────────────────────────

/// Device has no pending work.
pub open spec fn device_idle(dev: &RuntimeDevice) -> bool {
    dev@.pending_submissions.len() == 0
}

/// Device has live resources.
pub open spec fn device_has_resources(dev: &RuntimeDevice) -> bool {
    dev@.live_buffers > 0 || dev@.live_images > 0
}

/// Device buffer count.
pub open spec fn device_buffer_count(dev: &RuntimeDevice) -> nat {
    dev@.live_buffers
}

/// Device image count.
pub open spec fn device_image_count(dev: &RuntimeDevice) -> nat {
    dev@.live_images
}

/// Proof: creating a buffer preserves well-formedness.
pub proof fn lemma_create_buffer_exec_wf(dev: &RuntimeDevice)
    requires runtime_device_wf(dev),
    ensures runtime_device_wf(&RuntimeDevice {
        handle: dev.handle,
        state: Ghost(create_buffer_ghost(dev@)),
    }),
{
    lemma_create_buffer_preserves_well_formed(dev@);
}

/// Proof: destroying a buffer preserves well-formedness.
pub proof fn lemma_destroy_buffer_exec_wf(dev: &RuntimeDevice)
    requires
        runtime_device_wf(dev),
        dev@.live_buffers > 0,
    ensures runtime_device_wf(&RuntimeDevice {
        handle: dev.handle,
        state: Ghost(destroy_buffer_ghost(dev@)),
    }),
{
    lemma_destroy_buffer_preserves_well_formed(dev@);
}

/// Proof: wait idle preserves well-formedness.
pub proof fn lemma_wait_idle_exec_wf(dev: &RuntimeDevice)
    requires runtime_device_wf(dev),
    ensures runtime_device_wf(&RuntimeDevice {
        handle: dev.handle,
        state: Ghost(device_wait_idle_ghost(dev@)),
    }),
{
    lemma_wait_idle_preserves_well_formed(dev@);
}

/// Proof: create buffer increments live count.
pub proof fn lemma_create_buffer_exec_increments(dev: &RuntimeDevice)
    requires runtime_device_wf(dev),
    ensures create_buffer_ghost(dev@).live_buffers == dev@.live_buffers + 1,
{
    lemma_create_buffer_increments(dev@);
}

/// Proof: destroy buffer decrements live count.
pub proof fn lemma_destroy_buffer_exec_decrements(dev: &RuntimeDevice)
    requires
        runtime_device_wf(dev),
        dev@.live_buffers > 0,
    ensures destroy_buffer_ghost(dev@).live_buffers == (dev@.live_buffers - 1) as nat,
{
    lemma_destroy_buffer_decrements(dev@);
}

/// Proof: create image increments live count.
pub proof fn lemma_create_image_exec_increments(dev: &RuntimeDevice)
    requires runtime_device_wf(dev),
    ensures create_image_ghost(dev@).live_images == dev@.live_images + 1,
{
    lemma_create_image_increments(dev@);
}

} // verus!
