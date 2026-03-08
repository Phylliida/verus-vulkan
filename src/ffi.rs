use vstd::prelude::*;
use crate::device::*;
use crate::memory::*;
use crate::fence::*;
use crate::semaphore::*;
use crate::pipeline::*;
use crate::descriptor::*;
use crate::swapchain::*;
use crate::timeline_semaphore::*;
use crate::image_layout::*;
use crate::resource::*;
use crate::sync::*;
use crate::runtime::device::*;
use crate::runtime::fence::*;
use crate::runtime::semaphore::*;
use crate::runtime::memory::*;
use crate::runtime::pipeline::*;
use crate::runtime::command_buffer::*;
use crate::runtime::queue::*;
use crate::runtime::descriptor::*;
use crate::runtime::swapchain::*;
use crate::runtime::timeline_semaphore::*;

verus! {

// ═══════════════════════════════════════════════════════════════════════
// Device
// ═══════════════════════════════════════════════════════════════════════

/// FFI: create a logical device.
#[verifier::external_body]
pub fn vk_create_device(
    device_state: Ghost<DeviceState>,
) -> (out: RuntimeDevice)
    requires device_well_formed(device_state@),
    ensures out@ == device_state@, runtime_device_wf(&out),
{
    unimplemented!()
}

/// FFI: destroy a logical device.
#[verifier::external_body]
pub fn vk_destroy_device(dev: &mut RuntimeDevice)
    requires runtime_device_wf(&*old(dev)),
{
    unimplemented!()
}

/// FFI: wait for device idle.
#[verifier::external_body]
pub fn vk_device_wait_idle(dev: &mut RuntimeDevice)
    requires runtime_device_wf(&*old(dev)),
    ensures dev@ == device_wait_idle_ghost(old(dev)@),
{
    unimplemented!()
}

/// FFI: create a buffer.
#[verifier::external_body]
pub fn vk_create_buffer(dev: &mut RuntimeDevice)
    requires runtime_device_wf(&*old(dev)),
    ensures dev@ == create_buffer_ghost(old(dev)@),
{
    unimplemented!()
}

/// FFI: destroy a buffer.
#[verifier::external_body]
pub fn vk_destroy_buffer(dev: &mut RuntimeDevice)
    requires runtime_device_wf(&*old(dev)), old(dev)@.live_buffers > 0,
    ensures dev@ == destroy_buffer_ghost(old(dev)@),
{
    unimplemented!()
}

/// FFI: create an image.
#[verifier::external_body]
pub fn vk_create_image(dev: &mut RuntimeDevice)
    requires runtime_device_wf(&*old(dev)),
    ensures dev@ == create_image_ghost(old(dev)@),
{
    unimplemented!()
}

/// FFI: destroy an image.
#[verifier::external_body]
pub fn vk_destroy_image(dev: &mut RuntimeDevice)
    requires runtime_device_wf(&*old(dev)), old(dev)@.live_images > 0,
    ensures dev@ == destroy_image_ghost(old(dev)@),
{
    unimplemented!()
}

/// FFI: get a queue from the device.
#[verifier::external_body]
pub fn vk_get_device_queue(
    family_index: u32,
    queue_index: u32,
    queue_id: Ghost<nat>,
) -> (out: RuntimeQueue)
    ensures
        out.family_index == family_index,
        out.queue_index == queue_index,
        out.queue_id@ == queue_id@,
{
    unimplemented!()
}

// ═══════════════════════════════════════════════════════════════════════
// Memory
// ═══════════════════════════════════════════════════════════════════════

/// FFI: allocate device memory.
#[verifier::external_body]
pub fn vk_allocate_memory(
    id: Ghost<nat>,
    heap_index: Ghost<nat>,
    size: Ghost<nat>,
) -> (out: RuntimeAllocation)
    ensures
        out@.id == id@,
        out@.heap_index == heap_index@,
        out@.size == size@,
        out@.alive,
        out.mapped@ == false,
{
    unimplemented!()
}

/// FFI: free device memory.
#[verifier::external_body]
pub fn vk_free_memory(alloc: &mut RuntimeAllocation)
    requires runtime_alloc_wf(&*old(alloc)), old(alloc).mapped@ == false,
    ensures !alloc@.alive, alloc@.id == old(alloc)@.id,
{
    unimplemented!()
}

/// FFI: map memory.
#[verifier::external_body]
pub fn vk_map_memory(alloc: &mut RuntimeAllocation)
    requires runtime_alloc_wf(&*old(alloc)), old(alloc).mapped@ == false,
    ensures alloc.mapped@ == true, alloc@ == old(alloc)@,
{
    unimplemented!()
}

/// FFI: unmap memory.
#[verifier::external_body]
pub fn vk_unmap_memory(alloc: &mut RuntimeAllocation)
    requires runtime_alloc_wf(&*old(alloc)), old(alloc).mapped@ == true,
    ensures alloc.mapped@ == false, alloc@ == old(alloc)@,
{
    unimplemented!()
}

/// FFI: bind buffer memory.
#[verifier::external_body]
pub fn vk_bind_buffer_memory(
    _alloc: &RuntimeAllocation,
    _offset: u64,
)
    requires runtime_alloc_wf(_alloc),
{
    unimplemented!()
}

/// FFI: bind image memory.
#[verifier::external_body]
pub fn vk_bind_image_memory(
    _alloc: &RuntimeAllocation,
    _offset: u64,
)
    requires runtime_alloc_wf(_alloc),
{
    unimplemented!()
}

// ═══════════════════════════════════════════════════════════════════════
// Command Buffer
// ═══════════════════════════════════════════════════════════════════════

/// FFI: allocate a command buffer.
#[verifier::external_body]
pub fn vk_allocate_command_buffer(
    cb_state: Ghost<CommandBufferStatus>,
) -> (out: RuntimeCommandBuffer)
    ensures out.status@ == cb_state@,
{
    unimplemented!()
}

/// FFI: begin recording a command buffer.
#[verifier::external_body]
pub fn vk_begin_command_buffer(cb: &mut RuntimeCommandBuffer)
    requires !old(cb).in_render_pass@,
{
    unimplemented!()
}

/// FFI: end recording a command buffer.
#[verifier::external_body]
pub fn vk_end_command_buffer(cb: &mut RuntimeCommandBuffer)
    requires !old(cb).in_render_pass@,
{
    unimplemented!()
}

/// FFI: begin a render pass.
#[verifier::external_body]
pub fn vk_cmd_begin_render_pass(cb: &mut RuntimeCommandBuffer)
    requires !old(cb).in_render_pass@,
    ensures cb.in_render_pass@ == true,
{
    unimplemented!()
}

/// FFI: end a render pass.
#[verifier::external_body]
pub fn vk_cmd_end_render_pass(cb: &mut RuntimeCommandBuffer)
    requires old(cb).in_render_pass@,
    ensures cb.in_render_pass@ == false,
{
    unimplemented!()
}

/// FFI: draw.
#[verifier::external_body]
pub fn vk_cmd_draw(
    cb: &mut RuntimeCommandBuffer,
    _vertex_count: u32,
    _instance_count: u32,
    _first_vertex: u32,
    _first_instance: u32,
)
    requires old(cb).in_render_pass@,
{
    unimplemented!()
}

/// FFI: dispatch compute.
#[verifier::external_body]
pub fn vk_cmd_dispatch(
    cb: &mut RuntimeCommandBuffer,
    _group_count_x: u32,
    _group_count_y: u32,
    _group_count_z: u32,
)
    requires !old(cb).in_render_pass@,
{
    unimplemented!()
}

/// FFI: pipeline barrier.
#[verifier::external_body]
pub fn vk_cmd_pipeline_barrier(cb: &mut RuntimeCommandBuffer)
    requires !old(cb).in_render_pass@,
{
    unimplemented!()
}

/// FFI: bind a pipeline.
#[verifier::external_body]
pub fn vk_cmd_bind_pipeline(cb: &mut RuntimeCommandBuffer)
{
    unimplemented!()
}

/// FFI: bind descriptor sets.
#[verifier::external_body]
pub fn vk_cmd_bind_descriptor_sets(
    cb: &mut RuntimeCommandBuffer,
    _sets: Ghost<Seq<DescriptorSetState>>,
)
{
    unimplemented!()
}

// ═══════════════════════════════════════════════════════════════════════
// Sync
// ═══════════════════════════════════════════════════════════════════════

/// FFI: create a fence.
#[verifier::external_body]
pub fn vk_create_fence(
    id: Ghost<nat>,
    signaled: bool,
) -> (out: RuntimeFence)
    ensures out@ == create_fence_ghost(id@, signaled), runtime_fence_wf(&out),
{
    unimplemented!()
}

/// FFI: reset fences.
#[verifier::external_body]
pub fn vk_reset_fences(fence: &mut RuntimeFence)
    requires runtime_fence_wf(&*old(fence)),
    ensures fence@ == reset_fence_ghost(old(fence)@),
{
    unimplemented!()
}

/// FFI: wait for fences.
#[verifier::external_body]
pub fn vk_wait_for_fences(fence: &mut RuntimeFence, sub_id: Ghost<nat>)
    requires runtime_fence_wf(&*old(fence)),
    ensures fence@ == signal_fence_ghost(old(fence)@, sub_id@), fence@.signaled,
{
    unimplemented!()
}

/// FFI: create a binary semaphore.
#[verifier::external_body]
pub fn vk_create_semaphore(
    id: Ghost<nat>,
) -> (out: RuntimeSemaphore)
    ensures out@ == create_semaphore_ghost(id@), runtime_semaphore_wf(&out),
{
    unimplemented!()
}

/// FFI: create a timeline semaphore.
#[verifier::external_body]
pub fn vk_create_timeline_semaphore(
    handle: u64,
    id: Ghost<nat>,
    initial_value: u64,
) -> (out: RuntimeTimelineSemaphore)
    ensures
        out@ == initial_timeline(id@, initial_value as nat),
        runtime_timeline_wf(&out),
{
    unimplemented!()
}

/// FFI: signal a timeline semaphore from the host.
#[verifier::external_body]
pub fn vk_signal_semaphore(
    sem: &mut RuntimeTimelineSemaphore,
    value: u64,
)
    requires
        runtime_timeline_wf(&*old(sem)),
        signal_value_valid(old(sem)@, value as nat),
    ensures
        sem@ == submit_signal(old(sem)@, value as nat),
{
    unimplemented!()
}

// ═══════════════════════════════════════════════════════════════════════
// Queue
// ═══════════════════════════════════════════════════════════════════════

/// FFI: submit command buffers to a queue.
#[verifier::external_body]
pub fn vk_queue_submit(
    _queue: &RuntimeQueue,
    _command_buffers: Ghost<Seq<nat>>,
    _wait_semaphores: Ghost<Seq<nat>>,
    _signal_semaphores: Ghost<Seq<nat>>,
)
{
    unimplemented!()
}

/// FFI: wait for a queue to be idle.
#[verifier::external_body]
pub fn vk_queue_wait_idle(_queue: &RuntimeQueue)
{
    unimplemented!()
}

/// FFI: present to a queue.
#[verifier::external_body]
pub fn vk_queue_present(
    _queue: &RuntimeQueue,
    sc: &mut RuntimeSwapchain,
    idx: u64,
)
    requires
        runtime_swapchain_wf(&*old(sc)),
        can_present_image(&*old(sc), idx as nat),
    ensures
        sc@ == present_image(old(sc)@, idx as nat).unwrap(),
{
    unimplemented!()
}

// ═══════════════════════════════════════════════════════════════════════
// Pipeline
// ═══════════════════════════════════════════════════════════════════════

/// FFI: create a graphics pipeline.
#[verifier::external_body]
pub fn vk_create_graphics_pipeline(
    gps: Ghost<GraphicsPipelineState>,
) -> (out: RuntimeGraphicsPipeline)
    requires gps@.alive,
    ensures out@ == gps@, runtime_gfx_pipeline_wf(&out),
{
    unimplemented!()
}

/// FFI: create a compute pipeline.
#[verifier::external_body]
pub fn vk_create_compute_pipeline(
    cps: Ghost<ComputePipelineState>,
) -> (out: RuntimeComputePipeline)
    requires compute_pipeline_well_formed(cps@),
    ensures out@ == cps@, runtime_compute_pipeline_wf(&out),
{
    unimplemented!()
}

/// FFI: destroy a pipeline (graphics or compute).
#[verifier::external_body]
pub fn vk_destroy_pipeline(pipe: &mut RuntimeGraphicsPipeline)
    requires runtime_gfx_pipeline_wf(&*old(pipe)),
    ensures !pipe@.alive, pipe@.id == old(pipe)@.id,
{
    unimplemented!()
}

/// FFI: create a pipeline layout.
#[verifier::external_body]
pub fn vk_create_pipeline_layout() -> (handle: u64)
{
    unimplemented!()
}

/// FFI: destroy a pipeline layout.
#[verifier::external_body]
pub fn vk_destroy_pipeline_layout(_handle: u64)
{
    unimplemented!()
}

// ═══════════════════════════════════════════════════════════════════════
// Descriptor
// ═══════════════════════════════════════════════════════════════════════

/// FFI: create a descriptor set layout.
#[verifier::external_body]
pub fn vk_create_descriptor_set_layout(
    handle: u64,
    layout_state: Ghost<DescriptorSetLayoutState>,
) -> (out: RuntimeDescriptorSetLayout)
    requires layout_state@.alive, layout_well_formed(layout_state@),
    ensures out@ == layout_state@, runtime_dsl_wf(&out),
{
    unimplemented!()
}

/// FFI: create a descriptor pool.
#[verifier::external_body]
pub fn vk_create_descriptor_pool(
    handle: u64,
    id: Ghost<nat>,
    max_sets: u64,
) -> (out: RuntimeDescriptorPool)
    requires max_sets > 0,
    ensures
        runtime_pool_wf(&out),
        out@.id == id@,
        out@.max_sets == max_sets as nat,
        out@.allocated_sets == 0,
        pool_has_capacity(&out),
{
    unimplemented!()
}

/// FFI: allocate descriptor sets.
#[verifier::external_body]
pub fn vk_allocate_descriptor_sets(
    pool: &mut RuntimeDescriptorPool,
    handle: u64,
    set_id: Ghost<nat>,
    layout_id: Ghost<nat>,
) -> (out: RuntimeDescriptorSet)
    requires runtime_pool_wf(&*old(pool)), pool_has_capacity(&*old(pool)),
    ensures
        out@.id == set_id@,
        out@.layout_id == layout_id@,
        out@.pool_id == old(pool)@.id,
        pool@ == allocate_from_pool(old(pool)@),
{
    unimplemented!()
}

/// FFI: update descriptor sets.
#[verifier::external_body]
pub fn vk_update_descriptor_sets(
    ds: &mut RuntimeDescriptorSet,
    binding_num: Ghost<nat>,
    new_binding: Ghost<DescriptorBinding>,
)
    ensures ds@ == update_descriptor_binding(old(ds)@, binding_num@, new_binding@),
{
    unimplemented!()
}

/// FFI: destroy a descriptor pool.
#[verifier::external_body]
pub fn vk_destroy_descriptor_pool(pool: &mut RuntimeDescriptorPool)
    requires runtime_pool_wf(&*old(pool)),
    ensures !pool@.alive, pool@.id == old(pool)@.id,
{
    unimplemented!()
}

// ═══════════════════════════════════════════════════════════════════════
// Swapchain
// ═══════════════════════════════════════════════════════════════════════

/// FFI: create a swapchain.
#[verifier::external_body]
pub fn vk_create_swapchain(
    handle: u64,
    id: Ghost<nat>,
    image_count: u64,
) -> (out: RuntimeSwapchain)
    requires image_count > 0,
    ensures
        runtime_swapchain_wf(&out),
        out@.id == id@,
        out@.image_states.len() == image_count as nat,
        all_available(out@),
{
    unimplemented!()
}

/// FFI: acquire next image from swapchain.
#[verifier::external_body]
pub fn vk_acquire_next_image(
    sc: &mut RuntimeSwapchain,
    idx: u64,
)
    requires
        runtime_swapchain_wf(&*old(sc)),
        can_acquire_image(&*old(sc), idx as nat),
    ensures
        sc@ == acquire_image(old(sc)@, idx as nat).unwrap(),
        sc@.image_states[idx as int] == SwapchainImageState::Acquired,
{
    unimplemented!()
}

/// FFI: queue present (KHR extension).
#[verifier::external_body]
pub fn vk_queue_present_khr(
    _queue: &RuntimeQueue,
    sc: &mut RuntimeSwapchain,
    idx: u64,
)
    requires
        runtime_swapchain_wf(&*old(sc)),
        can_present_image(&*old(sc), idx as nat),
    ensures
        sc@ == present_image(old(sc)@, idx as nat).unwrap(),
{
    unimplemented!()
}

} // verus!
