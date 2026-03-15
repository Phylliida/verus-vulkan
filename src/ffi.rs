//! # FFI Convention
//!
//! Ghost parameters (Ghost<T>) appear right after `ctx: &VulkanContext`,
//! before concrete runtime parameters. This groups the "what we're proving"
//! with the context, keeping raw Vulkan parameters at the end.
//!
//! Pattern: `vk_create_foo(ctx, ghost_state, handle1, handle2, ...)`
//!          `vk_destroy_foo(ctx, runtime_obj)`

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
use crate::recording::*;
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
use crate::runtime::query_pool::*;
use crate::runtime::event::*;
use crate::runtime::acceleration_structure::*;
use crate::runtime::ray_tracing_pipeline::*;
use crate::query_pool::*;
use crate::event::*;
use crate::acceleration_structure::*;
use crate::ray_tracing_pipeline::*;
use crate::surface::*;
use crate::shader_module::*;
use crate::render_pass::*;
use crate::framebuffer::*;
use crate::command_pool::*;
use crate::runtime::render_pass::*;
use crate::runtime::framebuffer::*;
use crate::runtime::command_pool::*;
use crate::runtime::surface::*;
use crate::runtime::shader_module::*;
use crate::pipeline_layout::*;
use crate::shader_interface::*;

use ash::vk;
use ash::vk::Handle;
use crate::vk_context::VulkanContext;

/// Opaque Vulkan object handle (VkBuffer, VkImage, VkPipeline, etc.)
pub type VkHandle = u64;
/// Swapchain image index returned by vkAcquireNextImageKHR.
pub type ImageIndex = u64;

// ═══════════════════════════════════════════════════════════════════════════
// Ash helpers — pure Rust, outside verus!
// ═══════════════════════════════════════════════════════════════════════════

// ── Device helpers ──────────────────────────────────────────────────────

fn raw_device_handle(ctx: &VulkanContext) -> u64 {
    ctx.device.handle().as_raw()
}

fn raw_device_wait_idle(ctx: &VulkanContext) {
    unsafe { ctx.device.device_wait_idle() }.expect("device_wait_idle failed");
}

fn raw_create_buffer(ctx: &VulkanContext, size: u64, usage: u32, sharing_mode: u32) -> u64 {
    let ci = vk::BufferCreateInfo::default()
        .size(size)
        .usage(vk::BufferUsageFlags::from_raw(usage))
        .sharing_mode(if sharing_mode == 0 { vk::SharingMode::EXCLUSIVE }
            else { vk::SharingMode::CONCURRENT });
    unsafe { ctx.device.create_buffer(&ci, None) }.expect("create_buffer failed").as_raw()
}

fn raw_destroy_buffer(ctx: &VulkanContext, handle: u64) {
    unsafe { ctx.device.destroy_buffer(vk::Buffer::from_raw(handle), None) }
}

fn raw_create_image(
    ctx: &VulkanContext, width: u32, height: u32, depth: u32, format: u32,
    mip_levels: u32, array_layers: u32, samples: u32, tiling: u32, usage: u32,
) -> u64 {
    let ci = vk::ImageCreateInfo::default()
        .image_type(if depth > 1 { vk::ImageType::TYPE_3D }
            else if height > 1 { vk::ImageType::TYPE_2D }
            else { vk::ImageType::TYPE_1D })
        .format(vk::Format::from_raw(format as i32))
        .extent(vk::Extent3D { width, height, depth })
        .mip_levels(mip_levels).array_layers(array_layers)
        .samples(vk::SampleCountFlags::from_raw(samples))
        .tiling(if tiling == 0 { vk::ImageTiling::OPTIMAL } else { vk::ImageTiling::LINEAR })
        .usage(vk::ImageUsageFlags::from_raw(usage))
        .initial_layout(vk::ImageLayout::UNDEFINED);
    unsafe { ctx.device.create_image(&ci, None) }.expect("create_image failed").as_raw()
}

fn raw_destroy_image(ctx: &VulkanContext, handle: u64) {
    unsafe { ctx.device.destroy_image(vk::Image::from_raw(handle), None) }
}

fn raw_get_device_queue(ctx: &VulkanContext, family: u32, index: u32) -> u64 {
    unsafe { ctx.device.get_device_queue(family, index) }.as_raw()
}

// ── Memory helpers ──────────────────────────────────────────────────────

fn raw_allocate_memory(ctx: &VulkanContext, size_bytes: u64, mem_type_idx: u32) -> u64 {
    let ai = vk::MemoryAllocateInfo::default()
        .allocation_size(size_bytes).memory_type_index(mem_type_idx);
    unsafe { ctx.device.allocate_memory(&ai, None) }
        .expect("allocate_memory failed").as_raw()
}

fn raw_free_memory(ctx: &VulkanContext, handle: u64) {
    unsafe { ctx.device.free_memory(vk::DeviceMemory::from_raw(handle), None) }
}

fn raw_map_memory(ctx: &VulkanContext, handle: u64, offset: u64, size: u64) {
    unsafe {
        ctx.device.map_memory(
            vk::DeviceMemory::from_raw(handle), offset, size, vk::MemoryMapFlags::empty(),
        )
    }.expect("map_memory failed");
}

fn raw_unmap_memory(ctx: &VulkanContext, handle: u64) {
    unsafe { ctx.device.unmap_memory(vk::DeviceMemory::from_raw(handle)) }
}

fn raw_bind_buffer_memory(ctx: &VulkanContext, buf: u64, mem: u64, offset: u64) {
    unsafe {
        ctx.device.bind_buffer_memory(
            vk::Buffer::from_raw(buf), vk::DeviceMemory::from_raw(mem), offset,
        )
    }.expect("bind_buffer_memory failed");
}

fn raw_bind_image_memory(ctx: &VulkanContext, img: u64, mem: u64, offset: u64) {
    unsafe {
        ctx.device.bind_image_memory(
            vk::Image::from_raw(img), vk::DeviceMemory::from_raw(mem), offset,
        )
    }.expect("bind_image_memory failed");
}

// ── Command buffer helpers ──────────────────────────────────────────────

fn raw_allocate_command_buffer(ctx: &VulkanContext, pool: u64) -> u64 {
    let ai = vk::CommandBufferAllocateInfo::default()
        .command_pool(vk::CommandPool::from_raw(pool))
        .level(vk::CommandBufferLevel::PRIMARY).command_buffer_count(1);
    let cbs = unsafe { ctx.device.allocate_command_buffers(&ai) }
        .expect("allocate_command_buffers failed");
    cbs[0].as_raw()
}

fn raw_begin_command_buffer(ctx: &VulkanContext, cb: u64) {
    let bi = vk::CommandBufferBeginInfo::default();
    unsafe { ctx.device.begin_command_buffer(vk::CommandBuffer::from_raw(cb), &bi) }
        .expect("begin_command_buffer failed");
}

fn raw_end_command_buffer(ctx: &VulkanContext, cb: u64) {
    unsafe { ctx.device.end_command_buffer(vk::CommandBuffer::from_raw(cb)) }
        .expect("end_command_buffer failed");
}

fn raw_cmd_begin_render_pass(
    ctx: &VulkanContext, cb: u64, rp: u64, fb: u64, w: u32, h: u32,
    clear_r: f32, clear_g: f32, clear_b: f32, clear_a: f32,
) {
    let clear_values = [vk::ClearValue {
        color: vk::ClearColorValue { float32: [clear_r, clear_g, clear_b, clear_a] },
    }];
    let bi = vk::RenderPassBeginInfo::default()
        .render_pass(vk::RenderPass::from_raw(rp))
        .framebuffer(vk::Framebuffer::from_raw(fb))
        .render_area(vk::Rect2D {
            offset: vk::Offset2D { x: 0, y: 0 },
            extent: vk::Extent2D { width: w, height: h },
        })
        .clear_values(&clear_values);
    unsafe {
        ctx.device.cmd_begin_render_pass(
            vk::CommandBuffer::from_raw(cb), &bi, vk::SubpassContents::INLINE,
        );
    }
}

fn raw_cmd_end_render_pass(ctx: &VulkanContext, cb: u64) {
    unsafe { ctx.device.cmd_end_render_pass(vk::CommandBuffer::from_raw(cb)) }
}

fn raw_cmd_draw(ctx: &VulkanContext, cb: u64, vc: u32, ic: u32, fv: u32, fi: u32) {
    unsafe { ctx.device.cmd_draw(vk::CommandBuffer::from_raw(cb), vc, ic, fv, fi) }
}

fn raw_cmd_dispatch(ctx: &VulkanContext, cb: u64, gx: u32, gy: u32, gz: u32) {
    unsafe { ctx.device.cmd_dispatch(vk::CommandBuffer::from_raw(cb), gx, gy, gz) }
}

fn raw_cmd_pipeline_barrier(ctx: &VulkanContext, cb: u64, src: u32, dst: u32) {
    unsafe {
        ctx.device.cmd_pipeline_barrier(
            vk::CommandBuffer::from_raw(cb),
            vk::PipelineStageFlags::from_raw(src), vk::PipelineStageFlags::from_raw(dst),
            vk::DependencyFlags::empty(), &[], &[], &[],
        );
    }
}

fn raw_cmd_bind_pipeline(ctx: &VulkanContext, cb: u64, bp: u32, pipe: u64) {
    let bind = if bp == 0 { vk::PipelineBindPoint::GRAPHICS }
        else { vk::PipelineBindPoint::COMPUTE };
    unsafe {
        ctx.device.cmd_bind_pipeline(
            vk::CommandBuffer::from_raw(cb), bind, vk::Pipeline::from_raw(pipe),
        );
    }
}

fn raw_cmd_bind_descriptor_sets(ctx: &VulkanContext, cb: u64, bp: u32, layout: u64, first: u32, sets: &[u64]) {
    let bind = if bp == 0 { vk::PipelineBindPoint::GRAPHICS }
        else { vk::PipelineBindPoint::COMPUTE };
    let ds: Vec<vk::DescriptorSet> = sets.iter().map(|h| vk::DescriptorSet::from_raw(*h)).collect();
    unsafe {
        ctx.device.cmd_bind_descriptor_sets(
            vk::CommandBuffer::from_raw(cb), bind,
            vk::PipelineLayout::from_raw(layout), first, &ds, &[],
        );
    }
}

fn raw_cmd_draw_indexed(ctx: &VulkanContext, cb: u64, ic: u32, inst_c: u32, fi: u32, vo: i32, f_inst: u32) {
    unsafe { ctx.device.cmd_draw_indexed(vk::CommandBuffer::from_raw(cb), ic, inst_c, fi, vo, f_inst) }
}

fn raw_cmd_next_subpass(ctx: &VulkanContext, cb: u64) {
    unsafe { ctx.device.cmd_next_subpass(vk::CommandBuffer::from_raw(cb), vk::SubpassContents::INLINE) }
}

fn raw_cmd_copy_buffer(ctx: &VulkanContext, cb: u64, src: u64, dst: u64, size: u64) {
    let region = vk::BufferCopy { src_offset: 0, dst_offset: 0, size };
    unsafe {
        ctx.device.cmd_copy_buffer(
            vk::CommandBuffer::from_raw(cb),
            vk::Buffer::from_raw(src), vk::Buffer::from_raw(dst), &[region],
        );
    }
}

fn raw_cmd_copy_image(ctx: &VulkanContext, cb: u64, src: u64, dst: u64, width: u32, height: u32) {
    let region = vk::ImageCopy {
        src_subresource: vk::ImageSubresourceLayers { aspect_mask: vk::ImageAspectFlags::COLOR, mip_level: 0, base_array_layer: 0, layer_count: 1 },
        src_offset: vk::Offset3D { x: 0, y: 0, z: 0 },
        dst_subresource: vk::ImageSubresourceLayers { aspect_mask: vk::ImageAspectFlags::COLOR, mip_level: 0, base_array_layer: 0, layer_count: 1 },
        dst_offset: vk::Offset3D { x: 0, y: 0, z: 0 },
        extent: vk::Extent3D { width, height, depth: 1 },
    };
    unsafe {
        ctx.device.cmd_copy_image(
            vk::CommandBuffer::from_raw(cb),
            vk::Image::from_raw(src), vk::ImageLayout::TRANSFER_SRC_OPTIMAL,
            vk::Image::from_raw(dst), vk::ImageLayout::TRANSFER_DST_OPTIMAL,
            &[region],
        );
    }
}

fn raw_cmd_blit_image(ctx: &VulkanContext, cb: u64, src: u64, dst: u64, width: u32, height: u32) {
    let region = vk::ImageBlit {
        src_subresource: vk::ImageSubresourceLayers { aspect_mask: vk::ImageAspectFlags::COLOR, mip_level: 0, base_array_layer: 0, layer_count: 1 },
        src_offsets: [
            vk::Offset3D { x: 0, y: 0, z: 0 },
            vk::Offset3D { x: width as i32, y: height as i32, z: 1 },
        ],
        dst_subresource: vk::ImageSubresourceLayers { aspect_mask: vk::ImageAspectFlags::COLOR, mip_level: 0, base_array_layer: 0, layer_count: 1 },
        dst_offsets: [
            vk::Offset3D { x: 0, y: 0, z: 0 },
            vk::Offset3D { x: width as i32, y: height as i32, z: 1 },
        ],
    };
    unsafe {
        ctx.device.cmd_blit_image(
            vk::CommandBuffer::from_raw(cb),
            vk::Image::from_raw(src), vk::ImageLayout::TRANSFER_SRC_OPTIMAL,
            vk::Image::from_raw(dst), vk::ImageLayout::TRANSFER_DST_OPTIMAL,
            &[region], vk::Filter::NEAREST,
        );
    }
}

fn raw_cmd_copy_buffer_to_image(ctx: &VulkanContext, cb: u64, src_buf: u64, dst_img: u64, width: u32, height: u32) {
    let region = vk::BufferImageCopy {
        buffer_offset: 0, buffer_row_length: 0, buffer_image_height: 0,
        image_subresource: vk::ImageSubresourceLayers { aspect_mask: vk::ImageAspectFlags::COLOR, mip_level: 0, base_array_layer: 0, layer_count: 1 },
        image_offset: vk::Offset3D { x: 0, y: 0, z: 0 },
        image_extent: vk::Extent3D { width, height, depth: 1 },
    };
    unsafe {
        ctx.device.cmd_copy_buffer_to_image(
            vk::CommandBuffer::from_raw(cb),
            vk::Buffer::from_raw(src_buf), vk::Image::from_raw(dst_img),
            vk::ImageLayout::TRANSFER_DST_OPTIMAL, &[region],
        );
    }
}

fn raw_cmd_copy_image_to_buffer(ctx: &VulkanContext, cb: u64, src_img: u64, dst_buf: u64, width: u32, height: u32) {
    let region = vk::BufferImageCopy {
        buffer_offset: 0, buffer_row_length: 0, buffer_image_height: 0,
        image_subresource: vk::ImageSubresourceLayers { aspect_mask: vk::ImageAspectFlags::COLOR, mip_level: 0, base_array_layer: 0, layer_count: 1 },
        image_offset: vk::Offset3D { x: 0, y: 0, z: 0 },
        image_extent: vk::Extent3D { width, height, depth: 1 },
    };
    unsafe {
        ctx.device.cmd_copy_image_to_buffer(
            vk::CommandBuffer::from_raw(cb),
            vk::Image::from_raw(src_img), vk::ImageLayout::TRANSFER_SRC_OPTIMAL,
            vk::Buffer::from_raw(dst_buf), &[region],
        );
    }
}

fn raw_cmd_bind_vertex_buffers(ctx: &VulkanContext, cb: u64, first_binding: u32, buffer: u64, offset: u64) {
    unsafe {
        ctx.device.cmd_bind_vertex_buffers(
            vk::CommandBuffer::from_raw(cb), first_binding,
            &[vk::Buffer::from_raw(buffer)], &[offset],
        );
    }
}

fn raw_cmd_bind_index_buffer(ctx: &VulkanContext, cb: u64, buffer: u64, offset: u64, index_type: u32) {
    let it = if index_type == 0 { vk::IndexType::UINT16 } else { vk::IndexType::UINT32 };
    unsafe {
        ctx.device.cmd_bind_index_buffer(
            vk::CommandBuffer::from_raw(cb),
            vk::Buffer::from_raw(buffer), offset, it,
        );
    }
}

// ── Sync helpers ────────────────────────────────────────────────────────

fn raw_create_fence(ctx: &VulkanContext, signaled: bool) -> u64 {
    let mut flags = vk::FenceCreateFlags::empty();
    if signaled { flags |= vk::FenceCreateFlags::SIGNALED; }
    let ci = vk::FenceCreateInfo::default().flags(flags);
    unsafe { ctx.device.create_fence(&ci, None) }.expect("create_fence failed").as_raw()
}

fn raw_reset_fences(ctx: &VulkanContext, fence: u64) {
    unsafe { ctx.device.reset_fences(&[vk::Fence::from_raw(fence)]) }
        .expect("reset_fences failed");
}

fn raw_wait_for_fences(ctx: &VulkanContext, fence: u64, timeout: u64) {
    unsafe { ctx.device.wait_for_fences(&[vk::Fence::from_raw(fence)], true, timeout) }
        .expect("wait_for_fences failed");
}

fn raw_create_semaphore(ctx: &VulkanContext) -> u64 {
    let ci = vk::SemaphoreCreateInfo::default();
    unsafe { ctx.device.create_semaphore(&ci, None) }
        .expect("create_semaphore failed").as_raw()
}

fn raw_create_timeline_semaphore(ctx: &VulkanContext, initial: u64) -> u64 {
    let mut type_ci = vk::SemaphoreTypeCreateInfo::default()
        .semaphore_type(vk::SemaphoreType::TIMELINE).initial_value(initial);
    let ci = vk::SemaphoreCreateInfo::default().push_next(&mut type_ci);
    unsafe { ctx.device.create_semaphore(&ci, None) }
        .expect("create_timeline_semaphore failed").as_raw()
}

fn raw_signal_semaphore(ctx: &VulkanContext, sem: u64, value: u64) {
    let si = vk::SemaphoreSignalInfo::default()
        .semaphore(vk::Semaphore::from_raw(sem)).value(value);
    unsafe { ctx.device.signal_semaphore(&si) }.expect("signal_semaphore failed");
}

fn raw_destroy_semaphore(ctx: &VulkanContext, handle: u64) {
    unsafe { ctx.device.destroy_semaphore(vk::Semaphore::from_raw(handle), None) }
}

fn raw_destroy_timeline_semaphore(ctx: &VulkanContext, handle: u64) {
    unsafe { ctx.device.destroy_semaphore(vk::Semaphore::from_raw(handle), None) }
}

// ── Queue helpers ───────────────────────────────────────────────────────

fn raw_queue_submit(
    ctx: &VulkanContext, queue: u64, cbs: &[u64],
    wait_sems: &[u64], wait_stages: &[u32],
    sig_sems: &[u64], fence: u64,
) {
    let cb_h: Vec<vk::CommandBuffer> = cbs.iter().map(|h| vk::CommandBuffer::from_raw(*h)).collect();
    let ws: Vec<vk::Semaphore> = wait_sems.iter().map(|h| vk::Semaphore::from_raw(*h)).collect();
    let wd: Vec<vk::PipelineStageFlags> = wait_stages.iter().map(|s| vk::PipelineStageFlags::from_raw(*s)).collect();
    let ss: Vec<vk::Semaphore> = sig_sems.iter().map(|h| vk::Semaphore::from_raw(*h)).collect();
    let si = vk::SubmitInfo::default()
        .command_buffers(&cb_h).wait_semaphores(&ws)
        .wait_dst_stage_mask(&wd).signal_semaphores(&ss);
    let f = if fence == 0 { vk::Fence::null() } else { vk::Fence::from_raw(fence) };
    unsafe { ctx.device.queue_submit(vk::Queue::from_raw(queue), &[si], f) }
        .expect("queue_submit failed");
}

fn raw_queue_wait_idle(ctx: &VulkanContext, queue: u64) {
    unsafe { ctx.device.queue_wait_idle(vk::Queue::from_raw(queue)) }
        .expect("queue_wait_idle failed");
}

fn raw_queue_present(ctx: &VulkanContext, queue: u64, sc: u64, idx: u32, wait_sems: &[u64]) {
    let scs = [vk::SwapchainKHR::from_raw(sc)];
    let idxs = [idx];
    let ws: Vec<vk::Semaphore> = wait_sems.iter().map(|h| vk::Semaphore::from_raw(*h)).collect();
    let pi = vk::PresentInfoKHR::default()
        .swapchains(&scs).image_indices(&idxs).wait_semaphores(&ws);
    unsafe { ctx.swapchain_loader.queue_present(vk::Queue::from_raw(queue), &pi) }
        .expect("queue_present failed");
}

// ── Pipeline helpers ────────────────────────────────────────────────────

fn raw_create_graphics_pipeline(
    ctx: &VulkanContext, layout: u64, rp: u64, vert: u64, frag: u64,
) -> u64 {
    let vert_stage = vk::PipelineShaderStageCreateInfo::default()
        .stage(vk::ShaderStageFlags::VERTEX)
        .module(vk::ShaderModule::from_raw(vert))
        .name(c"main");
    let frag_stage = vk::PipelineShaderStageCreateInfo::default()
        .stage(vk::ShaderStageFlags::FRAGMENT)
        .module(vk::ShaderModule::from_raw(frag))
        .name(c"main");
    let stages = [vert_stage, frag_stage];
    let vertex_input = vk::PipelineVertexInputStateCreateInfo::default();
    let input_assembly = vk::PipelineInputAssemblyStateCreateInfo::default()
        .topology(vk::PrimitiveTopology::TRIANGLE_LIST);
    let viewport_state = vk::PipelineViewportStateCreateInfo::default()
        .viewport_count(1).scissor_count(1);
    let rasterization = vk::PipelineRasterizationStateCreateInfo::default()
        .polygon_mode(vk::PolygonMode::FILL)
        .cull_mode(vk::CullModeFlags::NONE)
        .front_face(vk::FrontFace::COUNTER_CLOCKWISE)
        .line_width(1.0);
    let multisample = vk::PipelineMultisampleStateCreateInfo::default()
        .rasterization_samples(vk::SampleCountFlags::TYPE_1);
    let blend_attachment = vk::PipelineColorBlendAttachmentState::default()
        .color_write_mask(vk::ColorComponentFlags::RGBA);
    let blend_attachments = [blend_attachment];
    let color_blend = vk::PipelineColorBlendStateCreateInfo::default()
        .attachments(&blend_attachments);
    let dynamic_states = [vk::DynamicState::VIEWPORT, vk::DynamicState::SCISSOR];
    let dynamic_state = vk::PipelineDynamicStateCreateInfo::default()
        .dynamic_states(&dynamic_states);
    let ci = vk::GraphicsPipelineCreateInfo::default()
        .stages(&stages)
        .vertex_input_state(&vertex_input)
        .input_assembly_state(&input_assembly)
        .viewport_state(&viewport_state)
        .rasterization_state(&rasterization)
        .multisample_state(&multisample)
        .color_blend_state(&color_blend)
        .dynamic_state(&dynamic_state)
        .layout(vk::PipelineLayout::from_raw(layout))
        .render_pass(vk::RenderPass::from_raw(rp))
        .subpass(0);
    unsafe { ctx.device.create_graphics_pipelines(vk::PipelineCache::null(), &[ci], None) }
        .expect("create_graphics_pipelines failed")[0].as_raw()
}

fn raw_create_compute_pipeline(ctx: &VulkanContext, layout: u64, shader: u64) -> u64 {
    let stage = vk::PipelineShaderStageCreateInfo::default()
        .stage(vk::ShaderStageFlags::COMPUTE)
        .module(vk::ShaderModule::from_raw(shader)).name(c"main");
    let ci = vk::ComputePipelineCreateInfo::default().stage(stage)
        .layout(vk::PipelineLayout::from_raw(layout));
    unsafe { ctx.device.create_compute_pipelines(vk::PipelineCache::null(), &[ci], None) }
        .expect("create_compute_pipelines failed")[0].as_raw()
}

fn raw_destroy_pipeline(ctx: &VulkanContext, pipe: u64) {
    unsafe { ctx.device.destroy_pipeline(vk::Pipeline::from_raw(pipe), None) }
}

fn raw_create_pipeline_layout(ctx: &VulkanContext, layouts: &[u64]) -> u64 {
    let ls: Vec<vk::DescriptorSetLayout> = layouts.iter()
        .map(|h| vk::DescriptorSetLayout::from_raw(*h)).collect();
    let ci = vk::PipelineLayoutCreateInfo::default().set_layouts(&ls);
    unsafe { ctx.device.create_pipeline_layout(&ci, None) }
        .expect("create_pipeline_layout failed").as_raw()
}

fn raw_destroy_pipeline_layout(ctx: &VulkanContext, layout: u64) {
    unsafe { ctx.device.destroy_pipeline_layout(vk::PipelineLayout::from_raw(layout), None) }
}

// ── Descriptor helpers ──────────────────────────────────────────────────

fn raw_create_descriptor_set_layout(ctx: &VulkanContext, binding_count: u32) -> u64 {
    let bindings: Vec<vk::DescriptorSetLayoutBinding> = (0..binding_count)
        .map(|i| vk::DescriptorSetLayoutBinding::default()
            .binding(i).descriptor_type(vk::DescriptorType::UNIFORM_BUFFER)
            .descriptor_count(1).stage_flags(vk::ShaderStageFlags::ALL))
        .collect();
    let ci = vk::DescriptorSetLayoutCreateInfo::default().bindings(&bindings);
    unsafe { ctx.device.create_descriptor_set_layout(&ci, None) }
        .expect("create_descriptor_set_layout failed").as_raw()
}

fn raw_create_descriptor_pool(ctx: &VulkanContext, max_sets: u32) -> u64 {
    let ps = [vk::DescriptorPoolSize {
        ty: vk::DescriptorType::UNIFORM_BUFFER, descriptor_count: max_sets,
    }];
    let ci = vk::DescriptorPoolCreateInfo::default().max_sets(max_sets).pool_sizes(&ps);
    unsafe { ctx.device.create_descriptor_pool(&ci, None) }
        .expect("create_descriptor_pool failed").as_raw()
}

fn raw_allocate_descriptor_sets(ctx: &VulkanContext, pool: u64, layout: u64) -> u64 {
    let ls = [vk::DescriptorSetLayout::from_raw(layout)];
    let ai = vk::DescriptorSetAllocateInfo::default()
        .descriptor_pool(vk::DescriptorPool::from_raw(pool)).set_layouts(&ls);
    unsafe { ctx.device.allocate_descriptor_sets(&ai) }
        .expect("allocate_descriptor_sets failed")[0].as_raw()
}

fn raw_update_descriptor_sets(ctx: &VulkanContext, ds: u64, binding: u32, ty: u32, buf: u64, offset: u64, range: u64) {
    let bi = [vk::DescriptorBufferInfo { buffer: vk::Buffer::from_raw(buf), offset, range }];
    let w = vk::WriteDescriptorSet::default()
        .dst_set(vk::DescriptorSet::from_raw(ds)).dst_binding(binding)
        .descriptor_type(vk::DescriptorType::from_raw(ty as i32)).buffer_info(&bi);
    unsafe { ctx.device.update_descriptor_sets(&[w], &[]) }
}

fn raw_destroy_descriptor_pool(ctx: &VulkanContext, pool: u64) {
    unsafe { ctx.device.destroy_descriptor_pool(vk::DescriptorPool::from_raw(pool), None) }
}

fn raw_destroy_descriptor_set_layout(ctx: &VulkanContext, handle: u64) {
    unsafe { ctx.device.destroy_descriptor_set_layout(vk::DescriptorSetLayout::from_raw(handle), None) }
}

// ── Swapchain helpers ───────────────────────────────────────────────────

fn raw_create_swapchain(ctx: &VulkanContext, surface: u64, count: u32, fmt: u32, w: u32, h: u32, pm: u32) -> u64 {
    let ci = vk::SwapchainCreateInfoKHR::default()
        .surface(vk::SurfaceKHR::from_raw(surface))
        .min_image_count(count)
        .image_format(vk::Format::from_raw(fmt as i32))
        .image_color_space(vk::ColorSpaceKHR::SRGB_NONLINEAR)
        .image_extent(vk::Extent2D { width: w, height: h })
        .image_array_layers(1)
        .image_usage(vk::ImageUsageFlags::COLOR_ATTACHMENT)
        .image_sharing_mode(vk::SharingMode::EXCLUSIVE)
        .pre_transform(vk::SurfaceTransformFlagsKHR::IDENTITY)
        .composite_alpha(vk::CompositeAlphaFlagsKHR::OPAQUE)
        .present_mode(vk::PresentModeKHR::from_raw(pm as i32))
        .clipped(true);
    unsafe { ctx.swapchain_loader.create_swapchain(&ci, None) }
        .expect("create_swapchain failed").as_raw()
}

fn raw_acquire_next_image(ctx: &VulkanContext, sc: u64, sem: u64, fence: u64, timeout: u64) -> u32 {
    let s = if sem == 0 { vk::Semaphore::null() } else { vk::Semaphore::from_raw(sem) };
    let f = if fence == 0 { vk::Fence::null() } else { vk::Fence::from_raw(fence) };
    let (idx, _) = unsafe {
        ctx.swapchain_loader.acquire_next_image(
            vk::SwapchainKHR::from_raw(sc), timeout, s, f,
        )
    }.expect("acquire_next_image failed");
    idx
}

fn raw_destroy_swapchain(ctx: &VulkanContext, handle: u64) {
    unsafe { ctx.swapchain_loader.destroy_swapchain(vk::SwapchainKHR::from_raw(handle), None) }
}

// ── Query Pool helpers ────────────────────────────────────────────────

fn raw_create_query_pool(ctx: &VulkanContext, count: u32, query_type: u32) -> u64 {
    let ci = vk::QueryPoolCreateInfo::default()
        .query_type(vk::QueryType::from_raw(query_type as i32))
        .query_count(count);
    unsafe { ctx.device.create_query_pool(&ci, None) }
        .expect("create_query_pool failed").as_raw()
}

fn raw_destroy_query_pool(ctx: &VulkanContext, handle: u64) {
    unsafe { ctx.device.destroy_query_pool(vk::QueryPool::from_raw(handle), None) }
}

fn raw_cmd_reset_query_pool(ctx: &VulkanContext, cb: u64, pool: u64, first: u32, count: u32) {
    unsafe {
        ctx.device.cmd_reset_query_pool(
            vk::CommandBuffer::from_raw(cb), vk::QueryPool::from_raw(pool), first, count,
        );
    }
}

fn raw_cmd_begin_query(ctx: &VulkanContext, cb: u64, pool: u64, index: u32) {
    unsafe {
        ctx.device.cmd_begin_query(
            vk::CommandBuffer::from_raw(cb), vk::QueryPool::from_raw(pool),
            index, vk::QueryControlFlags::empty(),
        );
    }
}

fn raw_cmd_end_query(ctx: &VulkanContext, cb: u64, pool: u64, index: u32) {
    unsafe {
        ctx.device.cmd_end_query(
            vk::CommandBuffer::from_raw(cb), vk::QueryPool::from_raw(pool), index,
        );
    }
}

// ── Event helpers ────────────────────────────────────────────────────

fn raw_create_event(ctx: &VulkanContext) -> u64 {
    let ci = vk::EventCreateInfo::default();
    unsafe { ctx.device.create_event(&ci, None) }
        .expect("create_event failed").as_raw()
}

fn raw_destroy_event(ctx: &VulkanContext, handle: u64) {
    unsafe { ctx.device.destroy_event(vk::Event::from_raw(handle), None) }
}

fn raw_set_event(ctx: &VulkanContext, handle: u64) {
    unsafe { ctx.device.set_event(vk::Event::from_raw(handle)) }
        .expect("set_event failed");
}

fn raw_reset_event(ctx: &VulkanContext, handle: u64) {
    unsafe { ctx.device.reset_event(vk::Event::from_raw(handle)) }
        .expect("reset_event failed");
}

fn raw_cmd_set_event(ctx: &VulkanContext, cb: u64, event: u64, stages: u32) {
    unsafe {
        ctx.device.cmd_set_event(
            vk::CommandBuffer::from_raw(cb),
            vk::Event::from_raw(event),
            vk::PipelineStageFlags::from_raw(stages),
        );
    }
}

fn raw_cmd_reset_event(ctx: &VulkanContext, cb: u64, event: u64, stages: u32) {
    unsafe {
        ctx.device.cmd_reset_event(
            vk::CommandBuffer::from_raw(cb),
            vk::Event::from_raw(event),
            vk::PipelineStageFlags::from_raw(stages),
        );
    }
}

// ── Indirect + Dynamic Rendering helpers ────────────────────────────────

fn raw_cmd_draw_indirect(ctx: &VulkanContext, cb: u64, buffer: u64, offset: u64, draw_count: u32, stride: u32) {
    unsafe {
        ctx.device.cmd_draw_indirect(
            vk::CommandBuffer::from_raw(cb),
            vk::Buffer::from_raw(buffer),
            offset,
            draw_count,
            stride,
        );
    }
}

fn raw_cmd_draw_indexed_indirect(ctx: &VulkanContext, cb: u64, buffer: u64, offset: u64, draw_count: u32, stride: u32) {
    unsafe {
        ctx.device.cmd_draw_indexed_indirect(
            vk::CommandBuffer::from_raw(cb),
            vk::Buffer::from_raw(buffer),
            offset,
            draw_count,
            stride,
        );
    }
}

fn raw_cmd_dispatch_indirect(ctx: &VulkanContext, cb: u64, buffer: u64, offset: u64) {
    unsafe {
        ctx.device.cmd_dispatch_indirect(
            vk::CommandBuffer::from_raw(cb),
            vk::Buffer::from_raw(buffer),
            offset,
        );
    }
}

fn raw_cmd_begin_rendering(ctx: &VulkanContext, cb: u64, width: u32, height: u32, layer_count: u32) {
    // Uses VK_KHR_dynamic_rendering (core in Vulkan 1.3)
    let rendering_info = vk::RenderingInfo::default()
        .render_area(vk::Rect2D {
            offset: vk::Offset2D { x: 0, y: 0 },
            extent: vk::Extent2D { width, height },
        })
        .layer_count(layer_count);
    unsafe {
        ctx.device.cmd_begin_rendering(
            vk::CommandBuffer::from_raw(cb),
            &rendering_info,
        );
    }
}

fn raw_cmd_end_rendering(ctx: &VulkanContext, cb: u64) {
    unsafe {
        ctx.device.cmd_end_rendering(
            vk::CommandBuffer::from_raw(cb),
        );
    }
}

// ── Viewport / Scissor / Push Constants helpers ─────────────────────────

fn raw_cmd_set_viewport(ctx: &VulkanContext, cb: u64, x: f32, y: f32, w: f32, h: f32, min_d: f32, max_d: f32) {
    let viewport = vk::Viewport { x, y, width: w, height: h, min_depth: min_d, max_depth: max_d };
    unsafe { ctx.device.cmd_set_viewport(vk::CommandBuffer::from_raw(cb), 0, &[viewport]) }
}

fn raw_cmd_set_scissor(ctx: &VulkanContext, cb: u64, x: i32, y: i32, w: u32, h: u32) {
    let scissor = vk::Rect2D {
        offset: vk::Offset2D { x, y },
        extent: vk::Extent2D { width: w, height: h },
    };
    unsafe { ctx.device.cmd_set_scissor(vk::CommandBuffer::from_raw(cb), 0, &[scissor]) }
}

fn raw_cmd_push_constants(ctx: &VulkanContext, cb: u64, layout: u64, stages: u32, offset: u32, data: &[u8]) {
    unsafe {
        ctx.device.cmd_push_constants(
            vk::CommandBuffer::from_raw(cb),
            vk::PipelineLayout::from_raw(layout),
            vk::ShaderStageFlags::from_raw(stages),
            offset,
            data,
        );
    }
}

// ── Dynamic state helpers ────────────────────────────────────────────────

fn raw_cmd_set_line_width(ctx: &VulkanContext, cb: u64, line_width: f32) {
    unsafe { ctx.device.cmd_set_line_width(vk::CommandBuffer::from_raw(cb), line_width) }
}

fn raw_cmd_set_depth_bias(ctx: &VulkanContext, cb: u64, constant_factor: f32, clamp: f32, slope_factor: f32) {
    unsafe { ctx.device.cmd_set_depth_bias(vk::CommandBuffer::from_raw(cb), constant_factor, clamp, slope_factor) }
}

fn raw_cmd_set_blend_constants(ctx: &VulkanContext, cb: u64, constants: [f32; 4]) {
    unsafe { ctx.device.cmd_set_blend_constants(vk::CommandBuffer::from_raw(cb), &constants) }
}

fn raw_cmd_set_depth_bounds(ctx: &VulkanContext, cb: u64, min: f32, max: f32) {
    unsafe { ctx.device.cmd_set_depth_bounds(vk::CommandBuffer::from_raw(cb), min, max) }
}

fn raw_cmd_set_stencil_compare_mask(ctx: &VulkanContext, cb: u64, face_mask: u32, compare_mask: u32) {
    unsafe {
        ctx.device.cmd_set_stencil_compare_mask(
            vk::CommandBuffer::from_raw(cb),
            vk::StencilFaceFlags::from_raw(face_mask),
            compare_mask,
        );
    }
}

fn raw_cmd_set_stencil_write_mask(ctx: &VulkanContext, cb: u64, face_mask: u32, write_mask: u32) {
    unsafe {
        ctx.device.cmd_set_stencil_write_mask(
            vk::CommandBuffer::from_raw(cb),
            vk::StencilFaceFlags::from_raw(face_mask),
            write_mask,
        );
    }
}

fn raw_cmd_set_stencil_reference(ctx: &VulkanContext, cb: u64, face_mask: u32, reference: u32) {
    unsafe {
        ctx.device.cmd_set_stencil_reference(
            vk::CommandBuffer::from_raw(cb),
            vk::StencilFaceFlags::from_raw(face_mask),
            reference,
        );
    }
}

// ── Buffer operations helpers ───────────────────────────────────────────

fn raw_cmd_fill_buffer(ctx: &VulkanContext, cb: u64, buffer: u64, offset: u64, size: u64, data: u32) {
    unsafe {
        ctx.device.cmd_fill_buffer(
            vk::CommandBuffer::from_raw(cb),
            vk::Buffer::from_raw(buffer),
            offset,
            size,
            data,
        );
    }
}

fn raw_cmd_update_buffer(ctx: &VulkanContext, cb: u64, buffer: u64, offset: u64, data: &[u8]) {
    unsafe {
        ctx.device.cmd_update_buffer(
            vk::CommandBuffer::from_raw(cb),
            vk::Buffer::from_raw(buffer),
            offset,
            data,
        );
    }
}

// ── Image clear & resolve helpers ───────────────────────────────────────

fn raw_cmd_clear_color_image(ctx: &VulkanContext, cb: u64, image: u64, layout: u32) {
    let clear = vk::ClearColorValue { float32: [0.0, 0.0, 0.0, 0.0] };
    let range = vk::ImageSubresourceRange {
        aspect_mask: vk::ImageAspectFlags::COLOR,
        base_mip_level: 0,
        level_count: vk::REMAINING_MIP_LEVELS,
        base_array_layer: 0,
        layer_count: vk::REMAINING_ARRAY_LAYERS,
    };
    unsafe {
        ctx.device.cmd_clear_color_image(
            vk::CommandBuffer::from_raw(cb),
            vk::Image::from_raw(image),
            vk::ImageLayout::from_raw(layout as i32),
            &clear,
            &[range],
        );
    }
}

fn raw_cmd_clear_depth_stencil_image(ctx: &VulkanContext, cb: u64, image: u64, layout: u32) {
    let clear = vk::ClearDepthStencilValue { depth: 1.0, stencil: 0 };
    let range = vk::ImageSubresourceRange {
        aspect_mask: vk::ImageAspectFlags::DEPTH | vk::ImageAspectFlags::STENCIL,
        base_mip_level: 0,
        level_count: vk::REMAINING_MIP_LEVELS,
        base_array_layer: 0,
        layer_count: vk::REMAINING_ARRAY_LAYERS,
    };
    unsafe {
        ctx.device.cmd_clear_depth_stencil_image(
            vk::CommandBuffer::from_raw(cb),
            vk::Image::from_raw(image),
            vk::ImageLayout::from_raw(layout as i32),
            &clear,
            &[range],
        );
    }
}

fn raw_cmd_clear_attachments(ctx: &VulkanContext, cb: u64) {
    // Ghost-only: caller specifies attachments externally.
    // Minimal stub — real usage would take attachment/rect params.
    let attachment = vk::ClearAttachment {
        aspect_mask: vk::ImageAspectFlags::COLOR,
        color_attachment: 0,
        clear_value: vk::ClearValue {
            color: vk::ClearColorValue { float32: [0.0, 0.0, 0.0, 0.0] },
        },
    };
    let rect = vk::ClearRect {
        rect: vk::Rect2D { offset: vk::Offset2D { x: 0, y: 0 }, extent: vk::Extent2D { width: 1, height: 1 } },
        base_array_layer: 0,
        layer_count: 1,
    };
    unsafe { ctx.device.cmd_clear_attachments(vk::CommandBuffer::from_raw(cb), &[attachment], &[rect]) }
}

fn raw_cmd_resolve_image(ctx: &VulkanContext, cb: u64, src: u64, dst: u64, width: u32, height: u32) {
    let region = vk::ImageResolve {
        src_subresource: vk::ImageSubresourceLayers {
            aspect_mask: vk::ImageAspectFlags::COLOR,
            mip_level: 0, base_array_layer: 0, layer_count: 1,
        },
        src_offset: vk::Offset3D { x: 0, y: 0, z: 0 },
        dst_subresource: vk::ImageSubresourceLayers {
            aspect_mask: vk::ImageAspectFlags::COLOR,
            mip_level: 0, base_array_layer: 0, layer_count: 1,
        },
        dst_offset: vk::Offset3D { x: 0, y: 0, z: 0 },
        extent: vk::Extent3D { width, height, depth: 1 },
    };
    unsafe {
        ctx.device.cmd_resolve_image(
            vk::CommandBuffer::from_raw(cb),
            vk::Image::from_raw(src), vk::ImageLayout::TRANSFER_SRC_OPTIMAL,
            vk::Image::from_raw(dst), vk::ImageLayout::TRANSFER_DST_OPTIMAL,
            &[region],
        );
    }
}

// ── Query command helpers ───────────────────────────────────────────────

fn raw_cmd_write_timestamp(ctx: &VulkanContext, cb: u64, stage: u32, pool: u64, query: u32) {
    unsafe {
        ctx.device.cmd_write_timestamp(
            vk::CommandBuffer::from_raw(cb),
            vk::PipelineStageFlags::from_raw(stage),
            vk::QueryPool::from_raw(pool),
            query,
        );
    }
}

fn raw_cmd_copy_query_pool_results(ctx: &VulkanContext, cb: u64, pool: u64, first: u32, count: u32, dst: u64, offset: u64, stride: u64, flags: u32) {
    unsafe {
        ctx.device.cmd_copy_query_pool_results(
            vk::CommandBuffer::from_raw(cb),
            vk::QueryPool::from_raw(pool),
            first,
            count,
            vk::Buffer::from_raw(dst),
            offset,
            stride,
            vk::QueryResultFlags::from_raw(flags),
        );
    }
}

// ── Sync helpers ────────────────────────────────────────────────────────

fn raw_cmd_wait_events(ctx: &VulkanContext, cb: u64, event: u64, src_stage: u32, dst_stage: u32) {
    unsafe {
        ctx.device.cmd_wait_events(
            vk::CommandBuffer::from_raw(cb),
            &[vk::Event::from_raw(event)],
            vk::PipelineStageFlags::from_raw(src_stage),
            vk::PipelineStageFlags::from_raw(dst_stage),
            &[],
            &[],
            &[],
        );
    }
}

// ── Surface helpers ──────────────────────────────────────────────────

fn raw_destroy_surface(ctx: &VulkanContext, handle: u64) {
    unsafe { ctx.surface_loader.destroy_surface(vk::SurfaceKHR::from_raw(handle), None) }
}

// ── Shader Module helpers ────────────────────────────────────────────

fn raw_create_shader_module(ctx: &VulkanContext, code: &[u32]) -> u64 {
    let ci = vk::ShaderModuleCreateInfo::default().code(code);
    unsafe { ctx.device.create_shader_module(&ci, None) }
        .expect("create_shader_module failed").as_raw()
}

fn raw_destroy_shader_module(ctx: &VulkanContext, handle: u64) {
    unsafe { ctx.device.destroy_shader_module(vk::ShaderModule::from_raw(handle), None) }
}

// ── Render Pass helpers ──────────────────────────────────────────────

fn raw_create_render_pass(ctx: &VulkanContext, format: u32, load_op: u32, store_op: u32, samples: u32) -> u64 {
    let attachment = vk::AttachmentDescription::default()
        .format(vk::Format::from_raw(format as i32))
        .samples(vk::SampleCountFlags::from_raw(samples))
        .load_op(match load_op {
            0 => vk::AttachmentLoadOp::LOAD,
            1 => vk::AttachmentLoadOp::CLEAR,
            2 => vk::AttachmentLoadOp::DONT_CARE,
            _ => panic!("invalid load_op"),
        })
        .store_op(match store_op {
            0 => vk::AttachmentStoreOp::STORE,
            1 => vk::AttachmentStoreOp::DONT_CARE,
            _ => panic!("invalid store_op"),
        })
        .stencil_load_op(vk::AttachmentLoadOp::DONT_CARE)
        .stencil_store_op(vk::AttachmentStoreOp::DONT_CARE)
        .initial_layout(vk::ImageLayout::UNDEFINED)
        .final_layout(vk::ImageLayout::PRESENT_SRC_KHR);
    let color_ref = vk::AttachmentReference {
        attachment: 0,
        layout: vk::ImageLayout::COLOR_ATTACHMENT_OPTIMAL,
    };
    let color_refs = [color_ref];
    let subpass = vk::SubpassDescription::default()
        .pipeline_bind_point(vk::PipelineBindPoint::GRAPHICS)
        .color_attachments(&color_refs);
    let dep = vk::SubpassDependency::default()
        .src_subpass(vk::SUBPASS_EXTERNAL)
        .dst_subpass(0)
        .src_stage_mask(vk::PipelineStageFlags::COLOR_ATTACHMENT_OUTPUT)
        .dst_stage_mask(vk::PipelineStageFlags::COLOR_ATTACHMENT_OUTPUT)
        .dst_access_mask(vk::AccessFlags::COLOR_ATTACHMENT_WRITE);
    let attachments = [attachment];
    let subpasses = [subpass];
    let dependencies = [dep];
    let ci = vk::RenderPassCreateInfo::default()
        .attachments(&attachments)
        .subpasses(&subpasses)
        .dependencies(&dependencies);
    unsafe { ctx.device.create_render_pass(&ci, None) }
        .expect("create_render_pass failed").as_raw()
}

fn raw_destroy_render_pass(ctx: &VulkanContext, handle: u64) {
    unsafe { ctx.device.destroy_render_pass(vk::RenderPass::from_raw(handle), None) }
}

// ── Image View helpers ──────────────────────────────────────────────

fn raw_create_image_view(ctx: &VulkanContext, image: u64, format: u32, aspect: u32) -> u64 {
    let ci = vk::ImageViewCreateInfo::default()
        .image(vk::Image::from_raw(image))
        .view_type(vk::ImageViewType::TYPE_2D)
        .format(vk::Format::from_raw(format as i32))
        .components(vk::ComponentMapping {
            r: vk::ComponentSwizzle::IDENTITY,
            g: vk::ComponentSwizzle::IDENTITY,
            b: vk::ComponentSwizzle::IDENTITY,
            a: vk::ComponentSwizzle::IDENTITY,
        })
        .subresource_range(vk::ImageSubresourceRange {
            aspect_mask: vk::ImageAspectFlags::from_raw(aspect),
            base_mip_level: 0,
            level_count: 1,
            base_array_layer: 0,
            layer_count: 1,
        });
    unsafe { ctx.device.create_image_view(&ci, None) }
        .expect("create_image_view failed").as_raw()
}

fn raw_destroy_image_view(ctx: &VulkanContext, handle: u64) {
    unsafe { ctx.device.destroy_image_view(vk::ImageView::from_raw(handle), None) }
}

// ── Framebuffer helpers ──────────────────────────────────────────────

fn raw_create_framebuffer(ctx: &VulkanContext, rp: u64, views: &[u64], w: u32, h: u32) -> u64 {
    let vk_views: Vec<vk::ImageView> = views.iter()
        .map(|v| vk::ImageView::from_raw(*v)).collect();
    let ci = vk::FramebufferCreateInfo::default()
        .render_pass(vk::RenderPass::from_raw(rp))
        .attachments(&vk_views)
        .width(w)
        .height(h)
        .layers(1);
    unsafe { ctx.device.create_framebuffer(&ci, None) }
        .expect("create_framebuffer failed").as_raw()
}

fn raw_destroy_framebuffer(ctx: &VulkanContext, handle: u64) {
    unsafe { ctx.device.destroy_framebuffer(vk::Framebuffer::from_raw(handle), None) }
}

// ── Command Pool helpers ─────────────────────────────────────────────

fn raw_create_command_pool(ctx: &VulkanContext, queue_family: u32, flags: u32) -> u64 {
    let ci = vk::CommandPoolCreateInfo::default()
        .queue_family_index(queue_family)
        .flags(vk::CommandPoolCreateFlags::from_raw(flags));
    unsafe { ctx.device.create_command_pool(&ci, None) }
        .expect("create_command_pool failed").as_raw()
}

fn raw_destroy_command_pool(ctx: &VulkanContext, handle: u64) {
    unsafe { ctx.device.destroy_command_pool(vk::CommandPool::from_raw(handle), None) }
}

// ── Swapchain Image Query helpers ────────────────────────────────────

fn raw_get_swapchain_images(ctx: &VulkanContext, swapchain: u64) -> Vec<u64> {
    let images = unsafe {
        ctx.swapchain_loader.get_swapchain_images(vk::SwapchainKHR::from_raw(swapchain))
    }.expect("get_swapchain_images failed");
    images.iter().map(|img| img.as_raw()).collect()
}

// ═══════════════════════════════════════════════════════════════════════════
// Verified FFI layer — inside verus!
// ═══════════════════════════════════════════════════════════════════════════

verus! {

// Register VulkanContext (external to verus!) as a known opaque type.
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExVulkanContext(VulkanContext);

// ═══════════════════════════════════════════════════════════════════════
// Device
// ═══════════════════════════════════════════════════════════════════════

/// FFI: create a logical device.
#[verifier::external_body]
pub fn vk_create_device(
    ctx: &VulkanContext,
    device_state: Ghost<DeviceState>,
) -> (out: RuntimeDevice)
    requires device_well_formed(device_state@),
    ensures out@ == device_state@, runtime_device_wf(&out),
{
    RuntimeDevice {
        handle: raw_device_handle(ctx),
        device_id: Ghost(0nat),
        state: Ghost(device_state@),
    }
}

/// FFI: destroy a logical device.
#[verifier::external_body]
pub fn vk_destroy_device(ctx: &VulkanContext, dev: &mut RuntimeDevice)
    requires runtime_device_wf(&*old(dev)),
{
    raw_device_wait_idle(ctx);
}

/// FFI: wait for device idle.
#[verifier::external_body]
pub fn vk_device_wait_idle(ctx: &VulkanContext, dev: &mut RuntimeDevice)
    requires runtime_device_wf(&*old(dev)),
    ensures dev@ == device_wait_idle_ghost(old(dev)@),
{
    raw_device_wait_idle(ctx);
}

/// FFI: create a buffer.
#[verifier::external_body]
pub fn vk_create_buffer(
    ctx: &VulkanContext,
    dev: &mut RuntimeDevice,
    size: u64,
    usage: u32,
    sharing_mode: u32,
) -> (buffer_handle: u64)
    requires runtime_device_wf(&*old(dev)),
    ensures dev@ == create_buffer_ghost(old(dev)@),
{
    raw_create_buffer(ctx, size, usage, sharing_mode)
}

/// FFI: destroy a buffer.
#[verifier::external_body]
pub fn vk_destroy_buffer(ctx: &VulkanContext, dev: &mut RuntimeDevice, buffer_handle: u64)
    requires runtime_device_wf(&*old(dev)), old(dev)@.live_buffers > 0,
    ensures dev@ == destroy_buffer_ghost(old(dev)@),
{
    raw_destroy_buffer(ctx, buffer_handle);
}

/// FFI: create an image.
#[verifier::external_body]
pub fn vk_create_image(
    ctx: &VulkanContext,
    dev: &mut RuntimeDevice,
    width: u32, height: u32, depth: u32, format: u32,
    mip_levels: u32, array_layers: u32, samples: u32, tiling: u32, usage: u32,
) -> (image_handle: u64)
    requires runtime_device_wf(&*old(dev)),
    ensures dev@ == create_image_ghost(old(dev)@),
{
    raw_create_image(ctx, width, height, depth, format, mip_levels, array_layers, samples, tiling, usage)
}

/// FFI: destroy an image.
#[verifier::external_body]
pub fn vk_destroy_image(ctx: &VulkanContext, dev: &mut RuntimeDevice, image_handle: u64)
    requires runtime_device_wf(&*old(dev)), old(dev)@.live_images > 0,
    ensures dev@ == destroy_image_ghost(old(dev)@),
{
    raw_destroy_image(ctx, image_handle);
}

/// FFI: get a queue from the device.
#[verifier::external_body]
pub fn vk_get_device_queue(
    ctx: &VulkanContext,
    family_index: u32,
    queue_index: u32,
    queue_id: Ghost<nat>,
) -> (out: RuntimeQueue)
    ensures
        out.family_index == family_index,
        out.queue_index == queue_index,
        out.queue_id@ == queue_id@,
{
    let h = raw_get_device_queue(ctx, family_index, queue_index);
    RuntimeQueue { handle: h, family_index, queue_index, queue_id: Ghost(queue_id@) }
}

// ═══════════════════════════════════════════════════════════════════════
// Memory
// ═══════════════════════════════════════════════════════════════════════

/// FFI: allocate device memory.
#[verifier::external_body]
pub fn vk_allocate_memory(
    ctx: &VulkanContext,
    id: Ghost<nat>,
    heap_index: Ghost<nat>,
    size: Ghost<nat>,
    memory_type_index: u32,
    size_bytes: u64,
) -> (out: RuntimeAllocation)
    ensures
        out@.id == id@,
        out@.heap_index == heap_index@,
        out@.size == size@,
        out@.alive,
        out.mapped@ == false,
{
    let h = raw_allocate_memory(ctx, size_bytes, memory_type_index);
    RuntimeAllocation {
        handle: h,
        state: Ghost(MemoryAllocation { id: id@, heap_index: heap_index@, size: size@, alive: true }),
        mapped: Ghost(false),
    }
}

/// FFI: free device memory.
#[verifier::external_body]
pub fn vk_free_memory(ctx: &VulkanContext, alloc: &mut RuntimeAllocation)
    requires runtime_alloc_wf(&*old(alloc)), old(alloc).mapped@ == false,
    ensures !alloc@.alive, alloc@.id == old(alloc)@.id,
{
    raw_free_memory(ctx, alloc.handle);
}

/// FFI: map memory.
#[verifier::external_body]
pub fn vk_map_memory(ctx: &VulkanContext, alloc: &mut RuntimeAllocation, offset: u64, size_bytes: u64)
    requires runtime_alloc_wf(&*old(alloc)), old(alloc).mapped@ == false,
    ensures alloc.mapped@ == true, alloc@ == old(alloc)@,
{
    raw_map_memory(ctx, alloc.handle, offset, size_bytes);
}

/// FFI: unmap memory.
#[verifier::external_body]
pub fn vk_unmap_memory(ctx: &VulkanContext, alloc: &mut RuntimeAllocation)
    requires runtime_alloc_wf(&*old(alloc)), old(alloc).mapped@ == true,
    ensures alloc.mapped@ == false, alloc@ == old(alloc)@,
{
    raw_unmap_memory(ctx, alloc.handle);
}

/// FFI: bind buffer memory.
#[verifier::external_body]
pub fn vk_bind_buffer_memory(ctx: &VulkanContext, alloc: &RuntimeAllocation, offset: u64, buffer_handle: u64)
    requires runtime_alloc_wf(alloc),
{
    raw_bind_buffer_memory(ctx, buffer_handle, alloc.handle, offset);
}

/// FFI: bind image memory.
#[verifier::external_body]
pub fn vk_bind_image_memory(ctx: &VulkanContext, alloc: &RuntimeAllocation, offset: u64, image_handle: u64)
    requires runtime_alloc_wf(alloc),
{
    raw_bind_image_memory(ctx, image_handle, alloc.handle, offset);
}

// ═══════════════════════════════════════════════════════════════════════
// Command Buffer
// ═══════════════════════════════════════════════════════════════════════

/// FFI: allocate a command buffer.
#[verifier::external_body]
pub fn vk_allocate_command_buffer(
    ctx: &VulkanContext,
    cb_state: Ghost<CommandBufferStatus>,
    command_pool_handle: u64,
) -> (out: RuntimeCommandBuffer)
    ensures out.status@ == cb_state@,
{
    let h = raw_allocate_command_buffer(ctx, command_pool_handle);
    RuntimeCommandBuffer {
        handle: h,
        cb_id: Ghost(0nat),
        status: Ghost(cb_state@),
        barrier_log: Ghost(Seq::empty()),
        in_render_pass: Ghost(false),
        recording_state: Ghost(RecordingState {
            bound_graphics_pipeline: None,
            bound_compute_pipeline: None,
            bound_descriptor_sets: Map::empty(),
            bound_set_layouts: Map::empty(),
            active_render_pass: None,
            bound_vertex_buffers: Map::empty(),
            bound_index_buffer: None,
            viewport_set: false,
            scissor_set: false,
            push_constants_set: false,
            bound_dynamic_offsets: Map::empty(),
            bound_graphics_layout: None,
            bound_compute_layout: None,
        }),
        recording_thread: Ghost(0nat),
    }
}

/// FFI: begin recording a command buffer.
#[verifier::external_body]
pub fn vk_begin_command_buffer(ctx: &VulkanContext, cb: &mut RuntimeCommandBuffer)
    requires !old(cb).in_render_pass@,
{
    raw_begin_command_buffer(ctx, cb.handle);
}

/// FFI: end recording a command buffer.
#[verifier::external_body]
pub fn vk_end_command_buffer(ctx: &VulkanContext, cb: &mut RuntimeCommandBuffer)
    requires !old(cb).in_render_pass@,
{
    raw_end_command_buffer(ctx, cb.handle);
}

/// FFI: begin a render pass with clear color.
#[verifier::external_body]
pub fn vk_cmd_begin_render_pass(
    ctx: &VulkanContext,
    cb: &mut RuntimeCommandBuffer,
    render_pass_handle: u64,
    framebuffer_handle: u64,
    width: u32,
    height: u32,
    clear_r: f32,
    clear_g: f32,
    clear_b: f32,
    clear_a: f32,
)
    requires !old(cb).in_render_pass@,
    ensures cb.in_render_pass@ == true,
{
    raw_cmd_begin_render_pass(ctx, cb.handle, render_pass_handle, framebuffer_handle, width, height, clear_r, clear_g, clear_b, clear_a);
}

/// FFI: end a render pass.
#[verifier::external_body]
pub fn vk_cmd_end_render_pass(ctx: &VulkanContext, cb: &mut RuntimeCommandBuffer)
    requires old(cb).in_render_pass@,
    ensures cb.in_render_pass@ == false,
{
    raw_cmd_end_render_pass(ctx, cb.handle);
}

/// FFI: draw.
#[verifier::external_body]
pub fn vk_cmd_draw(
    ctx: &VulkanContext,
    cb: &mut RuntimeCommandBuffer,
    vertex_count: u32,
    instance_count: u32,
    first_vertex: u32,
    first_instance: u32,
)
    requires old(cb).in_render_pass@,
{
    raw_cmd_draw(ctx, cb.handle, vertex_count, instance_count, first_vertex, first_instance);
}

/// FFI: dispatch compute.
#[verifier::external_body]
pub fn vk_cmd_dispatch(
    ctx: &VulkanContext,
    cb: &mut RuntimeCommandBuffer,
    group_count_x: u32,
    group_count_y: u32,
    group_count_z: u32,
)
    requires !old(cb).in_render_pass@,
{
    raw_cmd_dispatch(ctx, cb.handle, group_count_x, group_count_y, group_count_z);
}

/// FFI: pipeline barrier.
#[verifier::external_body]
pub fn vk_cmd_pipeline_barrier(ctx: &VulkanContext, cb: &mut RuntimeCommandBuffer, src_stage: u32, dst_stage: u32)
    requires !old(cb).in_render_pass@,
{
    raw_cmd_pipeline_barrier(ctx, cb.handle, src_stage, dst_stage);
}

/// FFI: bind a pipeline.
#[verifier::external_body]
pub fn vk_cmd_bind_pipeline(ctx: &VulkanContext, cb: &mut RuntimeCommandBuffer, bind_point: u32, pipeline_handle: u64)
{
    raw_cmd_bind_pipeline(ctx, cb.handle, bind_point, pipeline_handle);
}

/// FFI: bind descriptor sets.
#[verifier::external_body]
pub fn vk_cmd_bind_descriptor_sets(
    ctx: &VulkanContext,
    cb: &mut RuntimeCommandBuffer,
    _sets: Ghost<Seq<DescriptorSetState>>,
    bind_point: u32,
    layout_handle: u64,
    first_set: u32,
    set_handles: &[u64],
)
{
    raw_cmd_bind_descriptor_sets(ctx, cb.handle, bind_point, layout_handle, first_set, set_handles);
}

// ═══════════════════════════════════════════════════════════════════════
// Sync
// ═══════════════════════════════════════════════════════════════════════

/// FFI: create a fence.
#[verifier::external_body]
pub fn vk_create_fence(ctx: &VulkanContext, id: Ghost<nat>, signaled: bool) -> (out: RuntimeFence)
    ensures out@ == create_fence_ghost(id@, signaled), runtime_fence_wf(&out),
{
    let h = raw_create_fence(ctx, signaled);
    RuntimeFence { handle: h, state: Ghost(create_fence_ghost(id@, signaled)) }
}

/// FFI: reset fences.
#[verifier::external_body]
pub fn vk_reset_fences(ctx: &VulkanContext, fence: &mut RuntimeFence)
    requires runtime_fence_wf(&*old(fence)),
    ensures fence@ == reset_fence_ghost(old(fence)@),
{
    raw_reset_fences(ctx, fence.handle);
}

/// FFI: wait for fences.
#[verifier::external_body]
pub fn vk_wait_for_fences(ctx: &VulkanContext, fence: &mut RuntimeFence, sub_id: Ghost<nat>, timeout: u64)
    requires runtime_fence_wf(&*old(fence)),
    ensures fence@ == signal_fence_ghost(old(fence)@, sub_id@), fence@.signaled,
{
    raw_wait_for_fences(ctx, fence.handle, timeout);
}

/// FFI: create a binary semaphore.
#[verifier::external_body]
pub fn vk_create_semaphore(ctx: &VulkanContext, id: Ghost<nat>) -> (out: RuntimeSemaphore)
    ensures out@ == create_semaphore_ghost(id@), runtime_semaphore_wf(&out),
{
    let h = raw_create_semaphore(ctx);
    RuntimeSemaphore { handle: h, state: Ghost(create_semaphore_ghost(id@)) }
}

/// FFI: create a timeline semaphore.
#[verifier::external_body]
pub fn vk_create_timeline_semaphore(
    ctx: &VulkanContext,
    id: Ghost<nat>,
    initial_value: u64,
) -> (out: RuntimeTimelineSemaphore)
    ensures out@ == initial_timeline(id@, initial_value as nat), runtime_timeline_wf(&out),
{
    let h = raw_create_timeline_semaphore(ctx, initial_value);
    RuntimeTimelineSemaphore { handle: h, state: Ghost(initial_timeline(id@, initial_value as nat)) }
}

/// FFI: signal a timeline semaphore from the host.
#[verifier::external_body]
pub fn vk_signal_semaphore(ctx: &VulkanContext, sem: &mut RuntimeTimelineSemaphore, value: u64)
    requires runtime_timeline_wf(&*old(sem)), signal_value_valid(old(sem)@, value as nat),
    ensures sem@ == submit_signal(old(sem)@, value as nat),
{
    raw_signal_semaphore(ctx, sem.handle, value);
}

/// FFI: destroy a binary semaphore.
/// Caller must prove device is idle (no pending submission uses this semaphore).
#[verifier::external_body]
pub fn vk_destroy_semaphore(
    ctx: &VulkanContext,
    sem: &mut RuntimeSemaphore,
    dev: &RuntimeDevice,
)
    requires
        runtime_semaphore_wf(&*old(sem)),
        // Device must be idle — no pending work references this semaphore
        forall|i: int| 0 <= i < dev@.pending_submissions.len()
            ==> (#[trigger] dev@.pending_submissions[i]).completed,
    ensures sem@ == destroy_semaphore_ghost(old(sem)@), !sem@.alive,
{
    raw_destroy_semaphore(ctx, sem.handle);
    sem.state = Ghost(destroy_semaphore_ghost(sem.state@));
}

/// FFI: destroy a timeline semaphore.
/// Caller must prove device is idle (no pending signals/waits on this semaphore).
#[verifier::external_body]
pub fn vk_destroy_timeline_semaphore(
    ctx: &VulkanContext,
    sem: &mut RuntimeTimelineSemaphore,
    dev: &RuntimeDevice,
)
    requires
        runtime_timeline_wf(&*old(sem)),
        // Device must be idle — no pending work references this semaphore
        forall|i: int| 0 <= i < dev@.pending_submissions.len()
            ==> (#[trigger] dev@.pending_submissions[i]).completed,
    ensures sem@ == destroy_timeline_ghost(old(sem)@), !sem@.alive, sem@.id == old(sem)@.id,
{
    raw_destroy_timeline_semaphore(ctx, sem.handle);
    sem.state = Ghost(destroy_timeline_ghost(sem.state@));
}

// ═══════════════════════════════════════════════════════════════════════
// Queue
// ═══════════════════════════════════════════════════════════════════════

/// FFI: submit command buffers to a queue.
#[verifier::external_body]
pub fn vk_queue_submit(
    ctx: &VulkanContext,
    queue: &RuntimeQueue,
    _command_buffers: Ghost<Seq<nat>>,
    _wait_semaphores: Ghost<Seq<nat>>,
    _signal_semaphores: Ghost<Seq<nat>>,
    cb_handles: &[u64],
    wait_sem_handles: &[u64],
    wait_stages: &[u32],
    signal_sem_handles: &[u64],
    fence_handle: u64,
)
{
    raw_queue_submit(ctx, queue.handle, cb_handles, wait_sem_handles, wait_stages, signal_sem_handles, fence_handle);
}

/// FFI: wait for a queue to be idle.
#[verifier::external_body]
pub fn vk_queue_wait_idle(ctx: &VulkanContext, queue: &RuntimeQueue)
{
    raw_queue_wait_idle(ctx, queue.handle);
}

/// FFI: present to a queue.
#[verifier::external_body]
pub fn vk_queue_present(
    ctx: &VulkanContext,
    queue: &RuntimeQueue,
    sc: &mut RuntimeSwapchain,
    idx: u64,
    wait_sem_handles: &[u64],
)
    requires runtime_swapchain_wf(&*old(sc)), can_present_image(&*old(sc), idx as nat),
    ensures sc@ == present_image(old(sc)@, idx as nat).unwrap(),
{
    raw_queue_present(ctx, queue.handle, sc.handle, idx as u32, wait_sem_handles);
}

// ═══════════════════════════════════════════════════════════════════════
// Pipeline
// ═══════════════════════════════════════════════════════════════════════

/// FFI: create a graphics pipeline.
#[verifier::external_body]
pub fn vk_create_graphics_pipeline(
    ctx: &VulkanContext,
    gps: Ghost<GraphicsPipelineState>,
    layout_handle: u64,
    render_pass_handle: u64,
    vert_module_handle: u64,
    frag_module_handle: u64,
) -> (out: RuntimeGraphicsPipeline)
    requires gps@.alive,
    ensures out@ == gps@, runtime_gfx_pipeline_wf(&out),
{
    let h = raw_create_graphics_pipeline(ctx, layout_handle, render_pass_handle, vert_module_handle, frag_module_handle);
    RuntimeGraphicsPipeline { handle: h, state: Ghost(gps@) }
}

/// FFI: create a compute pipeline.
#[verifier::external_body]
pub fn vk_create_compute_pipeline(
    ctx: &VulkanContext,
    cps: Ghost<ComputePipelineState>,
    layout_handle: u64,
    shader_module_handle: u64,
) -> (out: RuntimeComputePipeline)
    requires compute_pipeline_well_formed(cps@),
    ensures out@ == cps@, runtime_compute_pipeline_wf(&out),
{
    let h = raw_create_compute_pipeline(ctx, layout_handle, shader_module_handle);
    RuntimeComputePipeline { handle: h, state: Ghost(cps@) }
}

/// FFI: destroy a pipeline (graphics or compute).
#[verifier::external_body]
pub fn vk_destroy_pipeline(ctx: &VulkanContext, pipe: &mut RuntimeGraphicsPipeline)
    requires runtime_gfx_pipeline_wf(&*old(pipe)),
    ensures !pipe@.alive, pipe@.id == old(pipe)@.id,
{
    raw_destroy_pipeline(ctx, pipe.handle);
}

/// FFI: create a pipeline layout.
#[verifier::external_body]
pub fn vk_create_pipeline_layout(ctx: &VulkanContext, set_layout_handles: &[u64]) -> (handle: u64)
{
    raw_create_pipeline_layout(ctx, set_layout_handles)
}

/// FFI: destroy a pipeline layout.
#[verifier::external_body]
pub fn vk_destroy_pipeline_layout(ctx: &VulkanContext, handle: u64)
{
    raw_destroy_pipeline_layout(ctx, handle);
}

// ═══════════════════════════════════════════════════════════════════════
// Descriptor
// ═══════════════════════════════════════════════════════════════════════

/// FFI: create a descriptor set layout.
#[verifier::external_body]
pub fn vk_create_descriptor_set_layout(
    ctx: &VulkanContext,
    layout_state: Ghost<DescriptorSetLayoutState>,
    binding_count: u32,
) -> (out: RuntimeDescriptorSetLayout)
    requires layout_state@.alive, layout_well_formed(layout_state@),
    ensures out@ == layout_state@, runtime_dsl_wf(&out),
{
    let h = raw_create_descriptor_set_layout(ctx, binding_count);
    RuntimeDescriptorSetLayout { handle: h, state: Ghost(layout_state@) }
}

/// FFI: create a descriptor pool.
#[verifier::external_body]
pub fn vk_create_descriptor_pool(
    ctx: &VulkanContext,
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
    let h = raw_create_descriptor_pool(ctx, max_sets as u32);
    RuntimeDescriptorPool {
        handle: h,
        state: Ghost(DescriptorPoolState { id: id@, max_sets: max_sets as nat, allocated_sets: 0nat, alive: true }),
    }
}

/// FFI: allocate descriptor sets.
#[verifier::external_body]
pub fn vk_allocate_descriptor_sets(
    ctx: &VulkanContext,
    pool: &mut RuntimeDescriptorPool,
    set_id: Ghost<nat>,
    layout_id: Ghost<nat>,
    layout_handle: u64,
) -> (out: RuntimeDescriptorSet)
    requires runtime_pool_wf(&*old(pool)), pool_has_capacity(&*old(pool)),
    ensures
        out@.id == set_id@,
        out@.layout_id == layout_id@,
        out@.pool_id == old(pool)@.id,
        pool@ == allocate_from_pool(old(pool)@),
{
    let h = raw_allocate_descriptor_sets(ctx, pool.handle, layout_handle);
    RuntimeDescriptorSet {
        handle: h,
        state: Ghost(DescriptorSetState { id: set_id@, layout_id: layout_id@, pool_id: pool.state@.id, bindings: Map::empty() }),
    }
}

/// FFI: update descriptor sets.
#[verifier::external_body]
pub fn vk_update_descriptor_sets(
    ctx: &VulkanContext,
    ds: &mut RuntimeDescriptorSet,
    binding_num: Ghost<nat>,
    new_binding: Ghost<DescriptorBinding>,
    binding_index: u32,
    descriptor_type: u32,
    buffer_handle: u64,
    offset: u64,
    range: u64,
)
    ensures ds@ == update_descriptor_binding(old(ds)@, binding_num@, new_binding@),
{
    raw_update_descriptor_sets(ctx, ds.handle, binding_index, descriptor_type, buffer_handle, offset, range);
}

/// FFI: destroy a descriptor pool.
#[verifier::external_body]
pub fn vk_destroy_descriptor_pool(ctx: &VulkanContext, pool: &mut RuntimeDescriptorPool)
    requires runtime_pool_wf(&*old(pool)),
    ensures !pool@.alive, pool@.id == old(pool)@.id,
{
    raw_destroy_descriptor_pool(ctx, pool.handle);
}

/// FFI: destroy a descriptor set layout.
/// Caller must prove device is idle (no pending submission references this layout).
#[verifier::external_body]
pub fn vk_destroy_descriptor_set_layout(
    ctx: &VulkanContext,
    dsl: &mut RuntimeDescriptorSetLayout,
    dev: &RuntimeDevice,
)
    requires
        runtime_dsl_wf(&*old(dsl)),
        // Device must be idle — no pending submission references descriptor sets using this layout
        forall|i: int| 0 <= i < dev@.pending_submissions.len()
            ==> (#[trigger] dev@.pending_submissions[i]).completed,
    ensures
        dsl@ == destroy_descriptor_set_layout_ghost(old(dsl)@),
        !dsl@.alive,
        dsl@.id == old(dsl)@.id,
{
    raw_destroy_descriptor_set_layout(ctx, dsl.handle);
    dsl.state = Ghost(destroy_descriptor_set_layout_ghost(dsl.state@));
}

// ═══════════════════════════════════════════════════════════════════════
// Swapchain
// ═══════════════════════════════════════════════════════════════════════

/// FFI: create a swapchain.
#[verifier::external_body]
pub fn vk_create_swapchain(
    ctx: &VulkanContext,
    id: Ghost<nat>,
    image_count: u64,
    surface_handle: u64,
    format: u32,
    width: u32,
    height: u32,
    present_mode: u32,
) -> (out: RuntimeSwapchain)
    requires image_count > 0,
    ensures
        runtime_swapchain_wf(&out),
        out@.id == id@,
        out@.image_states.len() == image_count as nat,
        all_available(out@),
{
    let h = raw_create_swapchain(ctx, surface_handle, image_count as u32, format, width, height, present_mode);
    RuntimeSwapchain {
        handle: h,
        state: Ghost(SwapchainState {
            id: id@,
            image_states: Seq::new(image_count as nat, |_i| SwapchainImageState::Available),
            retired: false,
            alive: true,
        }),
    }
}

/// FFI: acquire next swapchain image. Returns the image index chosen by the driver.
#[verifier::external_body]
pub fn vk_acquire_next_image(
    ctx: &VulkanContext,
    sc: &mut RuntimeSwapchain,
    semaphore_handle: u64,
    fence_handle: u64,
    timeout: u64,
) -> (idx: u64)
    requires runtime_swapchain_wf(&*old(sc)),
    ensures idx < sc@.image_states.len(),
{
    let actual = raw_acquire_next_image(ctx, sc.handle, semaphore_handle, fence_handle, timeout);
    actual as u64
}

/// FFI: queue present (KHR extension).
#[verifier::external_body]
pub fn vk_queue_present_khr(
    ctx: &VulkanContext,
    queue: &RuntimeQueue,
    sc: &mut RuntimeSwapchain,
    idx: u64,
    wait_sem_handles: &[u64],
)
    requires runtime_swapchain_wf(&*old(sc)), can_present_image(&*old(sc), idx as nat),
    ensures sc@ == present_image(old(sc)@, idx as nat).unwrap(),
{
    raw_queue_present(ctx, queue.handle, sc.handle, idx as u32, wait_sem_handles);
}

/// FFI: destroy a swapchain.
/// Caller must prove device is idle (no pending work uses swapchain images).
#[verifier::external_body]
pub fn vk_destroy_swapchain(
    ctx: &VulkanContext,
    sc: &mut RuntimeSwapchain,
    dev: &RuntimeDevice,
)
    requires
        runtime_swapchain_wf(&*old(sc)),
        // All images must be available (none in-flight)
        all_available(old(sc)@),
        // Device must be idle
        forall|i: int| 0 <= i < dev@.pending_submissions.len()
            ==> (#[trigger] dev@.pending_submissions[i]).completed,
    ensures
        sc@ == destroy_swapchain_ghost(old(sc)@),
        !sc@.alive,
{
    raw_destroy_swapchain(ctx, sc.handle);
    sc.state = Ghost(destroy_swapchain_ghost(sc.state@));
}

// ═══════════════════════════════════════════════════════════════════════
// Query Pool
// ═══════════════════════════════════════════════════════════════════════

/// FFI: create a query pool.
#[verifier::external_body]
pub fn vk_create_query_pool(
    ctx: &VulkanContext,
    id: Ghost<nat>,
    count: u32,
    query_type: u32,
) -> (out: RuntimeQueryPool)
    requires count > 0,
    ensures
        out@ == create_query_pool(id@, count as nat),
        runtime_query_pool_wf(&out),
{
    let h = raw_create_query_pool(ctx, count, query_type);
    RuntimeQueryPool {
        handle: h,
        state: Ghost(create_query_pool(id@, count as nat)),
    }
}

/// FFI: destroy a query pool.
#[verifier::external_body]
pub fn vk_destroy_query_pool(ctx: &VulkanContext, pool: &mut RuntimeQueryPool)
    requires runtime_query_pool_wf(&*old(pool)),
    ensures pool@ == destroy_query_pool(old(pool)@), !pool@.alive,
{
    raw_destroy_query_pool(ctx, pool.handle);
    pool.state = Ghost(destroy_query_pool(pool.state@));
}

/// FFI: reset queries in a command buffer.
#[verifier::external_body]
pub fn vk_cmd_reset_query_pool(
    ctx: &VulkanContext,
    cb_handle: u64,
    pool: &mut RuntimeQueryPool,
    first: u32,
    count: u32,
)
    requires
        runtime_query_pool_wf(&*old(pool)),
        first as nat + count as nat <= old(pool)@.query_count,
    ensures
        pool@ == reset_queries(old(pool)@, first as nat, count as nat),
        runtime_query_pool_wf(pool),
{
    raw_cmd_reset_query_pool(ctx, cb_handle, pool.handle, first, count);
    pool.state = Ghost(reset_queries(pool.state@, first as nat, count as nat));
}

/// FFI: begin a query.
#[verifier::external_body]
pub fn vk_cmd_begin_query(
    ctx: &VulkanContext,
    cb_handle: u64,
    pool: &mut RuntimeQueryPool,
    index: u32,
)
    requires begin_query_valid(old(pool)@, index as nat),
    ensures
        pool@ == begin_query(old(pool)@, index as nat),
        runtime_query_pool_wf(pool),
{
    raw_cmd_begin_query(ctx, cb_handle, pool.handle, index);
    pool.state = Ghost(begin_query(pool.state@, index as nat));
}

/// FFI: end a query.
#[verifier::external_body]
pub fn vk_cmd_end_query(
    ctx: &VulkanContext,
    cb_handle: u64,
    pool: &mut RuntimeQueryPool,
    index: u32,
)
    requires end_query_valid(old(pool)@, index as nat),
    ensures
        pool@ == end_query(old(pool)@, index as nat),
        runtime_query_pool_wf(pool),
{
    raw_cmd_end_query(ctx, cb_handle, pool.handle, index);
    pool.state = Ghost(end_query(pool.state@, index as nat));
}

// ═══════════════════════════════════════════════════════════════════════
// Event
// ═══════════════════════════════════════════════════════════════════════

/// FFI: create an event.
#[verifier::external_body]
pub fn vk_create_event(
    ctx: &VulkanContext,
    id: Ghost<nat>,
) -> (out: RuntimeEvent)
    ensures
        out@ == create_event(id@),
        runtime_event_wf(&out),
{
    let h = raw_create_event(ctx);
    RuntimeEvent {
        handle: h,
        state: Ghost(create_event(id@)),
    }
}

/// FFI: destroy an event.
#[verifier::external_body]
pub fn vk_destroy_event(ctx: &VulkanContext, event: &mut RuntimeEvent)
    requires runtime_event_wf(&*old(event)),
    ensures event@ == destroy_event(old(event)@), !event@.alive,
{
    raw_destroy_event(ctx, event.handle);
    event.state = Ghost(destroy_event(event.state@));
}

/// FFI: set an event from the host.
#[verifier::external_body]
pub fn vk_set_event(ctx: &VulkanContext, event: &mut RuntimeEvent, stages: Ghost<Set<nat>>)
    requires runtime_event_wf(&*old(event)),
    ensures event@ == set_event(old(event)@, stages@), runtime_event_wf(event),
{
    raw_set_event(ctx, event.handle);
    event.state = Ghost(set_event(event.state@, stages@));
}

/// FFI: reset an event from the host.
#[verifier::external_body]
pub fn vk_reset_event(ctx: &VulkanContext, event: &mut RuntimeEvent)
    requires runtime_event_wf(&*old(event)),
    ensures event@ == reset_event(old(event)@), runtime_event_wf(event),
{
    raw_reset_event(ctx, event.handle);
    event.state = Ghost(reset_event(event.state@));
}

/// FFI: set an event from a command buffer.
#[verifier::external_body]
pub fn vk_cmd_set_event(
    ctx: &VulkanContext,
    cb_handle: u64,
    event: &mut RuntimeEvent,
    stages_mask: u32,
    stages: Ghost<Set<nat>>,
)
    requires runtime_event_wf(&*old(event)),
    ensures event@ == set_event(old(event)@, stages@), runtime_event_wf(event),
{
    raw_cmd_set_event(ctx, cb_handle, event.handle, stages_mask);
    event.state = Ghost(set_event(event.state@, stages@));
}

/// FFI: reset an event from a command buffer.
#[verifier::external_body]
pub fn vk_cmd_reset_event(
    ctx: &VulkanContext,
    cb_handle: u64,
    event: &mut RuntimeEvent,
    stages_mask: u32,
)
    requires runtime_event_wf(&*old(event)),
    ensures event@ == reset_event(old(event)@), runtime_event_wf(event),
{
    raw_cmd_reset_event(ctx, cb_handle, event.handle, stages_mask);
    event.state = Ghost(reset_event(event.state@));
}

// ═══════════════════════════════════════════════════════════════════════
// Acceleration Structure (KHR extension)
// ═══════════════════════════════════════════════════════════════════════

/// FFI: create an acceleration structure.
#[verifier::external_body]
pub fn vk_create_acceleration_structure(
    ctx: &VulkanContext,
    as_state: Ghost<AccelerationStructureState>,
) -> (out: RuntimeAccelerationStructure)
    requires as_well_formed(as_state@),
    ensures out@ == as_state@, runtime_as_wf(&out),
{
    RuntimeAccelerationStructure {
        handle: 0, // Real handle would come from ash extension loader
        state: as_state,
    }
}

/// FFI: destroy an acceleration structure.
#[verifier::external_body]
pub fn vk_destroy_acceleration_structure(
    ctx: &VulkanContext,
    as_obj: &mut RuntimeAccelerationStructure,
)
    requires runtime_as_wf(&*old(as_obj)),
    ensures as_obj@ == destroy_as_ghost(old(as_obj)@), !as_obj@.alive,
{
    as_obj.state = Ghost(destroy_as_ghost(as_obj.state@));
}

/// FFI: build an acceleration structure.
#[verifier::external_body]
pub fn vk_cmd_build_acceleration_structure(
    ctx: &VulkanContext,
    cb_handle: u64,
    as_obj: &mut RuntimeAccelerationStructure,
    mode: Ghost<ASBuildMode>,
)
    requires
        runtime_as_wf(&*old(as_obj)),
        mode@ == ASBuildMode::Update ==> old(as_obj)@.built,
    ensures
        as_obj@ == build_as_ghost(old(as_obj)@, mode@),
        runtime_as_wf(as_obj),
        as_obj@.built,
{
    as_obj.state = Ghost(build_as_ghost(as_obj.state@, mode@));
}

/// FFI: compact an acceleration structure.
#[verifier::external_body]
pub fn vk_cmd_compact_acceleration_structure(
    ctx: &VulkanContext,
    cb_handle: u64,
    as_obj: &mut RuntimeAccelerationStructure,
)
    requires
        runtime_as_wf(&*old(as_obj)),
        old(as_obj)@.built,
    ensures as_obj@ == compact_as_ghost(old(as_obj)@), runtime_as_wf(as_obj),
{
    as_obj.state = Ghost(compact_as_ghost(as_obj.state@));
}

// ═══════════════════════════════════════════════════════════════════════
// Ray Tracing Pipeline (KHR extension)
// ═══════════════════════════════════════════════════════════════════════

/// FFI: create a ray tracing pipeline.
#[verifier::external_body]
pub fn vk_create_ray_tracing_pipeline(
    ctx: &VulkanContext,
    rt_state: Ghost<RayTracingPipelineState>,
) -> (out: RuntimeRayTracingPipeline)
    requires rt_pipeline_well_formed(rt_state@),
    ensures out@ == rt_state@, runtime_rt_pipeline_wf(&out),
{
    RuntimeRayTracingPipeline {
        handle: 0, // Real handle would come from ash extension loader
        state: rt_state,
    }
}

/// FFI: destroy a ray tracing pipeline.
#[verifier::external_body]
pub fn vk_destroy_ray_tracing_pipeline(
    ctx: &VulkanContext,
    pipe: &mut RuntimeRayTracingPipeline,
)
    requires runtime_rt_pipeline_wf(&*old(pipe)),
    ensures pipe@ == destroy_rt_pipeline_ghost(old(pipe)@), !pipe@.alive,
{
    // Reuses raw_destroy_pipeline since VkPipeline is the same handle type
    raw_destroy_pipeline(ctx, pipe.handle);
    pipe.state = Ghost(destroy_rt_pipeline_ghost(pipe.state@));
}

// ═══════════════════════════════════════════════════════════════════════
// Indirect + Dynamic Rendering
// ═══════════════════════════════════════════════════════════════════════

/// FFI: indirect draw.
#[verifier::external_body]
pub fn vk_cmd_draw_indirect(
    ctx: &VulkanContext,
    cb: &mut RuntimeCommandBuffer,
    buffer_handle: u64,
    offset: u64,
    draw_count: u32,
    stride: u32,
)
    requires old(cb).in_render_pass@,
{
    raw_cmd_draw_indirect(ctx, cb.handle, buffer_handle, offset, draw_count, stride);
}

/// FFI: indirect indexed draw.
#[verifier::external_body]
pub fn vk_cmd_draw_indexed_indirect(
    ctx: &VulkanContext,
    cb: &mut RuntimeCommandBuffer,
    buffer_handle: u64,
    offset: u64,
    draw_count: u32,
    stride: u32,
)
    requires old(cb).in_render_pass@,
{
    raw_cmd_draw_indexed_indirect(ctx, cb.handle, buffer_handle, offset, draw_count, stride);
}

/// FFI: indirect dispatch.
#[verifier::external_body]
pub fn vk_cmd_dispatch_indirect(
    ctx: &VulkanContext,
    cb: &mut RuntimeCommandBuffer,
    buffer_handle: u64,
    offset: u64,
)
    requires !old(cb).in_render_pass@,
{
    raw_cmd_dispatch_indirect(ctx, cb.handle, buffer_handle, offset);
}

/// FFI: begin dynamic rendering (VK_KHR_dynamic_rendering / Vulkan 1.3).
#[verifier::external_body]
pub fn vk_cmd_begin_rendering(
    ctx: &VulkanContext,
    cb: &mut RuntimeCommandBuffer,
    width: u32,
    height: u32,
    layer_count: u32,
)
    requires !old(cb).in_render_pass@,
    ensures cb.in_render_pass@ == true,
{
    raw_cmd_begin_rendering(ctx, cb.handle, width, height, layer_count);
}

/// FFI: end dynamic rendering.
#[verifier::external_body]
pub fn vk_cmd_end_rendering(
    ctx: &VulkanContext,
    cb: &mut RuntimeCommandBuffer,
)
    requires old(cb).in_render_pass@,
    ensures cb.in_render_pass@ == false,
{
    raw_cmd_end_rendering(ctx, cb.handle);
}

// ═══════════════════════════════════════════════════════════════════════
// Minimal FFI bridges — u64 handles only, no ghost state
// Called by the verified exec layer in command_buffer.rs
// ═══════════════════════════════════════════════════════════════════════

#[verifier::external_body]
pub fn ffi_cmd_draw(ctx: &VulkanContext, cb_handle: u64, vc: u32, ic: u32, fv: u32, fi: u32) {
    raw_cmd_draw(ctx, cb_handle, vc, ic, fv, fi);
}

#[verifier::external_body]
pub fn ffi_cmd_draw_indexed(ctx: &VulkanContext, cb_handle: u64, ic: u32, inst_c: u32, fi: u32, vo: i32, f_inst: u32) {
    raw_cmd_draw_indexed(ctx, cb_handle, ic, inst_c, fi, vo, f_inst);
}

#[verifier::external_body]
pub fn ffi_cmd_dispatch(ctx: &VulkanContext, cb_handle: u64, gx: u32, gy: u32, gz: u32) {
    raw_cmd_dispatch(ctx, cb_handle, gx, gy, gz);
}

#[verifier::external_body]
pub fn ffi_cmd_pipeline_barrier(ctx: &VulkanContext, cb_handle: u64, src: u32, dst: u32) {
    raw_cmd_pipeline_barrier(ctx, cb_handle, src, dst);
}

#[verifier::external_body]
pub fn ffi_cmd_bind_pipeline(ctx: &VulkanContext, cb_handle: u64, bp: u32, pipe: u64) {
    raw_cmd_bind_pipeline(ctx, cb_handle, bp, pipe);
}

#[verifier::external_body]
pub fn ffi_cmd_begin_render_pass(ctx: &VulkanContext, cb_handle: u64, rp: u64, fb: u64, w: u32, h: u32, clear_r: f32, clear_g: f32, clear_b: f32, clear_a: f32) {
    raw_cmd_begin_render_pass(ctx, cb_handle, rp, fb, w, h, clear_r, clear_g, clear_b, clear_a);
}

#[verifier::external_body]
pub fn ffi_cmd_end_render_pass(ctx: &VulkanContext, cb_handle: u64) {
    raw_cmd_end_render_pass(ctx, cb_handle);
}

#[verifier::external_body]
pub fn ffi_cmd_next_subpass(ctx: &VulkanContext, cb_handle: u64) {
    raw_cmd_next_subpass(ctx, cb_handle);
}

#[verifier::external_body]
pub fn ffi_cmd_copy_buffer(ctx: &VulkanContext, cb_handle: u64, src: u64, dst: u64, size: u64) {
    raw_cmd_copy_buffer(ctx, cb_handle, src, dst, size);
}

#[verifier::external_body]
pub fn ffi_cmd_copy_image(ctx: &VulkanContext, cb_handle: u64, src: u64, dst: u64, width: u32, height: u32) {
    raw_cmd_copy_image(ctx, cb_handle, src, dst, width, height);
}

#[verifier::external_body]
pub fn ffi_cmd_blit_image(ctx: &VulkanContext, cb_handle: u64, src: u64, dst: u64, width: u32, height: u32) {
    raw_cmd_blit_image(ctx, cb_handle, src, dst, width, height);
}

#[verifier::external_body]
pub fn ffi_cmd_copy_buffer_to_image(ctx: &VulkanContext, cb_handle: u64, src_buf: u64, dst_img: u64, width: u32, height: u32) {
    raw_cmd_copy_buffer_to_image(ctx, cb_handle, src_buf, dst_img, width, height);
}

#[verifier::external_body]
pub fn ffi_cmd_copy_image_to_buffer(ctx: &VulkanContext, cb_handle: u64, src_img: u64, dst_buf: u64, width: u32, height: u32) {
    raw_cmd_copy_image_to_buffer(ctx, cb_handle, src_img, dst_buf, width, height);
}

#[verifier::external_body]
pub fn ffi_cmd_draw_indirect(ctx: &VulkanContext, cb_handle: u64, buffer: u64, offset: u64, draw_count: u32, stride: u32) {
    raw_cmd_draw_indirect(ctx, cb_handle, buffer, offset, draw_count, stride);
}

#[verifier::external_body]
pub fn ffi_cmd_draw_indexed_indirect(ctx: &VulkanContext, cb_handle: u64, buffer: u64, offset: u64, draw_count: u32, stride: u32) {
    raw_cmd_draw_indexed_indirect(ctx, cb_handle, buffer, offset, draw_count, stride);
}

#[verifier::external_body]
pub fn ffi_cmd_dispatch_indirect(ctx: &VulkanContext, cb_handle: u64, buffer: u64, offset: u64) {
    raw_cmd_dispatch_indirect(ctx, cb_handle, buffer, offset);
}

#[verifier::external_body]
pub fn ffi_cmd_begin_rendering(ctx: &VulkanContext, cb_handle: u64, width: u32, height: u32, layer_count: u32) {
    raw_cmd_begin_rendering(ctx, cb_handle, width, height, layer_count);
}

#[verifier::external_body]
pub fn ffi_cmd_end_rendering(ctx: &VulkanContext, cb_handle: u64) {
    raw_cmd_end_rendering(ctx, cb_handle);
}

#[verifier::external_body]
pub fn ffi_cmd_bind_vertex_buffers(ctx: &VulkanContext, cb_handle: u64, first_binding: u32, buffer: u64, offset: u64) {
    raw_cmd_bind_vertex_buffers(ctx, cb_handle, first_binding, buffer, offset);
}

#[verifier::external_body]
pub fn ffi_cmd_bind_index_buffer(ctx: &VulkanContext, cb_handle: u64, buffer: u64, offset: u64, index_type: u32) {
    raw_cmd_bind_index_buffer(ctx, cb_handle, buffer, offset, index_type);
}

#[verifier::external_body]
pub fn ffi_begin_command_buffer(ctx: &VulkanContext, cb_handle: u64) {
    raw_begin_command_buffer(ctx, cb_handle);
}

#[verifier::external_body]
pub fn ffi_end_command_buffer(ctx: &VulkanContext, cb_handle: u64) {
    raw_end_command_buffer(ctx, cb_handle);
}

#[verifier::external_body]
pub fn ffi_cmd_bind_descriptor_sets(ctx: &VulkanContext, cb_handle: u64, bp: u32, layout: u64, first: u32, sets: &[u64]) {
    raw_cmd_bind_descriptor_sets(ctx, cb_handle, bp, layout, first, sets);
}

#[verifier::external_body]
pub fn ffi_cmd_set_viewport(ctx: &VulkanContext, cb_handle: u64, x: f32, y: f32, w: f32, h: f32, min_d: f32, max_d: f32) {
    raw_cmd_set_viewport(ctx, cb_handle, x, y, w, h, min_d, max_d);
}

#[verifier::external_body]
pub fn ffi_cmd_set_scissor(ctx: &VulkanContext, cb_handle: u64, x: i32, y: i32, w: u32, h: u32) {
    raw_cmd_set_scissor(ctx, cb_handle, x, y, w, h);
}

#[verifier::external_body]
pub fn ffi_cmd_push_constants(ctx: &VulkanContext, cb_handle: u64, layout: u64, stages: u32, offset: u32, data: &[u8]) {
    raw_cmd_push_constants(ctx, cb_handle, layout, stages, offset, data);
}

// ── Query Pool command bridges ───────────────────────────────────────

#[verifier::external_body]
pub fn ffi_cmd_reset_query_pool(ctx: &VulkanContext, cb_handle: u64, pool_handle: u64, first: u32, count: u32) {
    raw_cmd_reset_query_pool(ctx, cb_handle, pool_handle, first, count);
}

#[verifier::external_body]
pub fn ffi_cmd_begin_query(ctx: &VulkanContext, cb_handle: u64, pool_handle: u64, index: u32) {
    raw_cmd_begin_query(ctx, cb_handle, pool_handle, index);
}

#[verifier::external_body]
pub fn ffi_cmd_end_query(ctx: &VulkanContext, cb_handle: u64, pool_handle: u64, index: u32) {
    raw_cmd_end_query(ctx, cb_handle, pool_handle, index);
}

// ── Event command bridges ────────────────────────────────────────────

#[verifier::external_body]
pub fn ffi_cmd_set_event(ctx: &VulkanContext, cb_handle: u64, event_handle: u64, stages_mask: u32) {
    raw_cmd_set_event(ctx, cb_handle, event_handle, stages_mask);
}

#[verifier::external_body]
pub fn ffi_cmd_reset_event(ctx: &VulkanContext, cb_handle: u64, event_handle: u64, stages_mask: u32) {
    raw_cmd_reset_event(ctx, cb_handle, event_handle, stages_mask);
}

// ── Acceleration Structure command bridges ───────────────────────────

#[verifier::external_body]
pub fn ffi_cmd_build_acceleration_structure(ctx: &VulkanContext, cb_handle: u64) {
    // No raw_* exists — VulkanContext lacks khr::acceleration_structure::Device.
    // Ghost-only stub for CB invariant enforcement.
}

#[verifier::external_body]
pub fn ffi_cmd_compact_acceleration_structure(ctx: &VulkanContext, cb_handle: u64) {
    // No raw_* exists — ghost-only stub.
}

// ── Dynamic state command bridges ───────────────────────────────────

#[verifier::external_body]
pub fn ffi_cmd_set_line_width(ctx: &VulkanContext, cb_handle: u64, line_width: f32) {
    raw_cmd_set_line_width(ctx, cb_handle, line_width);
}

#[verifier::external_body]
pub fn ffi_cmd_set_depth_bias(ctx: &VulkanContext, cb_handle: u64, constant_factor: f32, clamp: f32, slope_factor: f32) {
    raw_cmd_set_depth_bias(ctx, cb_handle, constant_factor, clamp, slope_factor);
}

#[verifier::external_body]
pub fn ffi_cmd_set_blend_constants(ctx: &VulkanContext, cb_handle: u64, c0: f32, c1: f32, c2: f32, c3: f32) {
    raw_cmd_set_blend_constants(ctx, cb_handle, [c0, c1, c2, c3]);
}

#[verifier::external_body]
pub fn ffi_cmd_set_depth_bounds(ctx: &VulkanContext, cb_handle: u64, min: f32, max: f32) {
    raw_cmd_set_depth_bounds(ctx, cb_handle, min, max);
}

#[verifier::external_body]
pub fn ffi_cmd_set_stencil_compare_mask(ctx: &VulkanContext, cb_handle: u64, face_mask: u32, compare_mask: u32) {
    raw_cmd_set_stencil_compare_mask(ctx, cb_handle, face_mask, compare_mask);
}

#[verifier::external_body]
pub fn ffi_cmd_set_stencil_write_mask(ctx: &VulkanContext, cb_handle: u64, face_mask: u32, write_mask: u32) {
    raw_cmd_set_stencil_write_mask(ctx, cb_handle, face_mask, write_mask);
}

#[verifier::external_body]
pub fn ffi_cmd_set_stencil_reference(ctx: &VulkanContext, cb_handle: u64, face_mask: u32, reference: u32) {
    raw_cmd_set_stencil_reference(ctx, cb_handle, face_mask, reference);
}

// ── Buffer operation command bridges ────────────────────────────────

#[verifier::external_body]
pub fn ffi_cmd_fill_buffer(ctx: &VulkanContext, cb_handle: u64, buffer: u64, offset: u64, size: u64, data: u32) {
    raw_cmd_fill_buffer(ctx, cb_handle, buffer, offset, size, data);
}

#[verifier::external_body]
pub fn ffi_cmd_update_buffer(ctx: &VulkanContext, cb_handle: u64, buffer: u64, offset: u64, data: &[u8]) {
    raw_cmd_update_buffer(ctx, cb_handle, buffer, offset, data);
}

// ── Image clear & resolve command bridges ───────────────────────────

#[verifier::external_body]
pub fn ffi_cmd_clear_color_image(ctx: &VulkanContext, cb_handle: u64, image: u64, layout: u32) {
    raw_cmd_clear_color_image(ctx, cb_handle, image, layout);
}

#[verifier::external_body]
pub fn ffi_cmd_clear_depth_stencil_image(ctx: &VulkanContext, cb_handle: u64, image: u64, layout: u32) {
    raw_cmd_clear_depth_stencil_image(ctx, cb_handle, image, layout);
}

#[verifier::external_body]
pub fn ffi_cmd_clear_attachments(ctx: &VulkanContext, cb_handle: u64) {
    raw_cmd_clear_attachments(ctx, cb_handle);
}

#[verifier::external_body]
pub fn ffi_cmd_resolve_image(ctx: &VulkanContext, cb_handle: u64, src: u64, dst: u64, width: u32, height: u32) {
    raw_cmd_resolve_image(ctx, cb_handle, src, dst, width, height);
}

// ── Query command bridges ───────────────────────────────────────────

#[verifier::external_body]
pub fn ffi_cmd_write_timestamp(ctx: &VulkanContext, cb_handle: u64, stage: u32, pool_handle: u64, query: u32) {
    raw_cmd_write_timestamp(ctx, cb_handle, stage, pool_handle, query);
}

#[verifier::external_body]
pub fn ffi_cmd_copy_query_pool_results(ctx: &VulkanContext, cb_handle: u64, pool_handle: u64, first: u32, count: u32, dst: u64, offset: u64, stride: u64, flags: u32) {
    raw_cmd_copy_query_pool_results(ctx, cb_handle, pool_handle, first, count, dst, offset, stride, flags);
}

// ── Sync command bridges ────────────────────────────────────────────

#[verifier::external_body]
pub fn ffi_cmd_wait_events(ctx: &VulkanContext, cb_handle: u64, event_handle: u64, src_stage: u32, dst_stage: u32) {
    raw_cmd_wait_events(ctx, cb_handle, event_handle, src_stage, dst_stage);
}

// ── Indirect count command bridges (ghost stubs — needs VK 1.2) ─────

#[verifier::external_body]
pub fn ffi_cmd_draw_indirect_count(ctx: &VulkanContext, cb_handle: u64, buffer: u64, offset: u64, count_buffer: u64, count_offset: u64, max_draw_count: u32, stride: u32) {
    // Ghost stub — VulkanContext lacks khr::draw_indirect_count::Device.
    // The verified wrapper enforces all preconditions at the spec level.
}

#[verifier::external_body]
pub fn ffi_cmd_draw_indexed_indirect_count(ctx: &VulkanContext, cb_handle: u64, buffer: u64, offset: u64, count_buffer: u64, count_offset: u64, max_draw_count: u32, stride: u32) {
    // Ghost stub.
}

// ── Ray tracing command bridges (ghost stubs) ───────────────────────

#[verifier::external_body]
pub fn ffi_cmd_trace_rays(ctx: &VulkanContext, cb_handle: u64) {
    // Ghost stub — VulkanContext lacks khr::ray_tracing_pipeline::Device.
}

#[verifier::external_body]
pub fn ffi_cmd_trace_rays_indirect(ctx: &VulkanContext, cb_handle: u64, buffer: u64) {
    // Ghost stub.
}

// ── Debug utils command bridges (ghost stubs) ───────────────────────

#[verifier::external_body]
pub fn ffi_cmd_begin_debug_utils_label(ctx: &VulkanContext, cb_handle: u64) {
    // Ghost stub — needs ext::debug_utils::Instance.
}

#[verifier::external_body]
pub fn ffi_cmd_end_debug_utils_label(ctx: &VulkanContext, cb_handle: u64) {
    // Ghost stub.
}

#[verifier::external_body]
pub fn ffi_cmd_insert_debug_utils_label(ctx: &VulkanContext, cb_handle: u64) {
    // Ghost stub.
}

// ── Extension command bridges (ghost stubs) ─────────────────────────

#[verifier::external_body]
pub fn ffi_cmd_dispatch_base(ctx: &VulkanContext, cb_handle: u64, bx: u32, by: u32, bz: u32, gx: u32, gy: u32, gz: u32) {
    // Ghost stub — Vulkan 1.1.
}

#[verifier::external_body]
pub fn ffi_cmd_draw_mesh_tasks(ctx: &VulkanContext, cb_handle: u64, gx: u32, gy: u32, gz: u32) {
    // Ghost stub — VK_EXT_mesh_shader.
}

#[verifier::external_body]
pub fn ffi_cmd_draw_mesh_tasks_indirect(ctx: &VulkanContext, cb_handle: u64, buffer: u64, offset: u64, draw_count: u32, stride: u32) {
    // Ghost stub.
}

#[verifier::external_body]
pub fn ffi_cmd_draw_mesh_tasks_indirect_count(ctx: &VulkanContext, cb_handle: u64, buffer: u64, offset: u64, count_buffer: u64, count_offset: u64, max_draw_count: u32, stride: u32) {
    // Ghost stub.
}

#[verifier::external_body]
pub fn ffi_cmd_begin_transform_feedback(ctx: &VulkanContext, cb_handle: u64) {
    // Ghost stub — VK_EXT_transform_feedback.
}

#[verifier::external_body]
pub fn ffi_cmd_end_transform_feedback(ctx: &VulkanContext, cb_handle: u64) {
    // Ghost stub.
}

#[verifier::external_body]
pub fn ffi_cmd_pipeline_barrier2(ctx: &VulkanContext, cb_handle: u64) {
    // Ghost stub — Vulkan 1.3 vkCmdPipelineBarrier2.
}

// ── Extended dynamic state command bridges (ghost stubs — VK 1.3) ───

#[verifier::external_body]
pub fn ffi_cmd_set_cull_mode(ctx: &VulkanContext, cb_handle: u64, cull_mode: u32) {
    // Ghost stub — vkCmdSetCullMode (Vulkan 1.3).
}

#[verifier::external_body]
pub fn ffi_cmd_set_front_face(ctx: &VulkanContext, cb_handle: u64, front_face: u32) {
    // Ghost stub — vkCmdSetFrontFace (Vulkan 1.3).
}

#[verifier::external_body]
pub fn ffi_cmd_set_primitive_topology(ctx: &VulkanContext, cb_handle: u64, topology: u32) {
    // Ghost stub — vkCmdSetPrimitiveTopology (Vulkan 1.3).
}

#[verifier::external_body]
pub fn ffi_cmd_set_depth_test_enable(ctx: &VulkanContext, cb_handle: u64, enable: u32) {
    // Ghost stub — vkCmdSetDepthTestEnable (Vulkan 1.3).
}

#[verifier::external_body]
pub fn ffi_cmd_set_depth_write_enable(ctx: &VulkanContext, cb_handle: u64, enable: u32) {
    // Ghost stub — vkCmdSetDepthWriteEnable (Vulkan 1.3).
}

#[verifier::external_body]
pub fn ffi_cmd_set_depth_compare_op(ctx: &VulkanContext, cb_handle: u64, compare_op: u32) {
    // Ghost stub — vkCmdSetDepthCompareOp (Vulkan 1.3).
}

#[verifier::external_body]
pub fn ffi_cmd_set_depth_bounds_test_enable(ctx: &VulkanContext, cb_handle: u64, enable: u32) {
    // Ghost stub — vkCmdSetDepthBoundsTestEnable (Vulkan 1.3).
}

#[verifier::external_body]
pub fn ffi_cmd_set_stencil_test_enable(ctx: &VulkanContext, cb_handle: u64, enable: u32) {
    // Ghost stub — vkCmdSetStencilTestEnable (Vulkan 1.3).
}

#[verifier::external_body]
pub fn ffi_cmd_set_stencil_op(ctx: &VulkanContext, cb_handle: u64, face_mask: u32, fail_op: u32, pass_op: u32, depth_fail_op: u32, compare_op: u32) {
    // Ghost stub — vkCmdSetStencilOp (Vulkan 1.3).
}

#[verifier::external_body]
pub fn ffi_cmd_set_rasterizer_discard_enable(ctx: &VulkanContext, cb_handle: u64, enable: u32) {
    // Ghost stub — vkCmdSetRasterizerDiscardEnable (Vulkan 1.3).
}

// ── Push descriptor command bridges (ghost stubs) ───────────────────

#[verifier::external_body]
pub fn ffi_cmd_push_descriptor_set(ctx: &VulkanContext, cb_handle: u64, bind_point: u32, layout: u64, set_index: u32) {
    // Ghost stub — vkCmdPushDescriptorSetKHR.
}

// ── Fragment shading rate command bridges (ghost stubs) ─────────────

#[verifier::external_body]
pub fn ffi_cmd_set_fragment_shading_rate(ctx: &VulkanContext, cb_handle: u64, width: u32, height: u32, combiner0: u32, combiner1: u32) {
    // Ghost stub — vkCmdSetFragmentShadingRateKHR.
}

// ── Shader object command bridges (ghost stubs) ─────────────────────

#[verifier::external_body]
pub fn ffi_cmd_bind_shaders(ctx: &VulkanContext, cb_handle: u64, stage_count: u32) {
    // Ghost stub — vkCmdBindShadersEXT.
}

// ═══════════════════════════════════════════════════════════════════════
// Round 4 — Triangle-ready FFI (hardened)
// ═══════════════════════════════════════════════════════════════════════

// ── Surface FFI ─────────────────────────────────────────────────────

/// Wrap a caller-provided surface handle with ghost state.
/// Surface creation is platform-specific (winit/ash-window provides the raw handle).
#[verifier::external_body]
pub fn vk_create_surface(
    ctx: &VulkanContext,
    id: Ghost<nat>,
    handle: u64,
) -> (out: RuntimeSurface)
    ensures
        out@ == (SurfaceState { id: id@, alive: true }),
        runtime_surface_wf(&out),
{
    RuntimeSurface {
        handle,
        state: Ghost(SurfaceState { id: id@, alive: true }),
    }
}

/// Destroy a surface.
/// Caller must prove no live swapchain references this surface.
#[verifier::external_body]
pub fn vk_destroy_surface(
    ctx: &VulkanContext,
    surface: &mut RuntimeSurface,
    dev: &RuntimeDevice,
    // Ghost: caller attests no live swapchain is bound to this surface
    no_live_swapchains: Ghost<bool>,
)
    requires
        runtime_surface_wf(&*old(surface)),
        // Device must be idle — no pending work referencing the surface
        forall|i: int| 0 <= i < dev@.pending_submissions.len()
            ==> (#[trigger] dev@.pending_submissions[i]).completed,
        // Caller attests no swapchain is alive on this surface
        no_live_swapchains@,
    ensures
        surface@ == destroy_surface_ghost(old(surface)@),
        !surface@.alive,
{
    raw_destroy_surface(ctx, surface.handle);
    surface.state = Ghost(destroy_surface_ghost(surface.state@));
}

// ── Shader Module FFI ────────────────────────────────────────────────

/// Create a shader module from SPIR-V code.
#[verifier::external_body]
pub fn vk_create_shader_module(
    ctx: &VulkanContext,
    state: Ghost<ShaderModuleState>,
    code: &[u32],
) -> (out: RuntimeShaderModule)
    requires state@.alive,
    ensures
        out@ == state@,
        runtime_shader_module_wf(&out),
{
    let h = raw_create_shader_module(ctx, code);
    RuntimeShaderModule { handle: h, state: Ghost(state@) }
}

/// Destroy a shader module.
/// Safe to destroy after pipeline creation — Vulkan copies the module at pipeline creation time.
#[verifier::external_body]
pub fn vk_destroy_shader_module(
    ctx: &VulkanContext,
    sm: &mut RuntimeShaderModule,
)
    requires runtime_shader_module_wf(&*old(sm)),
    ensures
        sm@ == destroy_shader_module_ghost(old(sm)@),
        !sm@.alive,
{
    raw_destroy_shader_module(ctx, sm.handle);
    sm.state = Ghost(destroy_shader_module_ghost(sm.state@));
}

// ── Render Pass FFI ──────────────────────────────────────────────────

/// Create a render pass (single attachment, single subpass — covers triangle case).
#[verifier::external_body]
pub fn vk_create_render_pass(
    ctx: &VulkanContext,
    rps: Ghost<RenderPassState>,
    format: u32,
    load_op: u32,
    store_op: u32,
    samples: u32,
) -> (out: RuntimeRenderPass)
    requires render_pass_well_formed(rps@), rps@.alive,
    ensures out@ == rps@, runtime_render_pass_wf(&out),
{
    let h = raw_create_render_pass(ctx, format, load_op, store_op, samples);
    RuntimeRenderPass { handle: h, state: Ghost(rps@) }
}

/// Destroy a render pass.
/// Caller must prove device is idle and no live framebuffers reference this render pass.
#[verifier::external_body]
pub fn vk_destroy_render_pass(
    ctx: &VulkanContext,
    rp: &mut RuntimeRenderPass,
    dev: &RuntimeDevice,
    // Ghost: caller attests no live framebuffer references this render pass
    no_live_framebuffers: Ghost<bool>,
)
    requires
        runtime_render_pass_wf(&*old(rp)),
        // Device must be idle
        forall|i: int| 0 <= i < dev@.pending_submissions.len()
            ==> (#[trigger] dev@.pending_submissions[i]).completed,
        // Caller attests no framebuffer references this render pass
        no_live_framebuffers@,
    ensures
        rp@ == destroy_render_pass_ghost(old(rp)@),
        !rp@.alive,
{
    raw_destroy_render_pass(ctx, rp.handle);
    rp.state = Ghost(destroy_render_pass_ghost(rp.state@));
}

// ── Image View FFI ───────────────────────────────────────────────────

/// Create an image view (2D, 1 mip, 1 layer).
/// Caller must provide a live swapchain that owns the image.
#[verifier::external_body]
pub fn vk_create_image_view(
    ctx: &VulkanContext,
    state: Ghost<ImageViewState>,
    sc: &RuntimeSwapchain,
    image_handle: u64,
    format: u32,
    aspect: u32,
) -> (out: RuntimeImageView)
    requires
        state@.alive,
        // Swapchain must be alive — it owns the images
        runtime_swapchain_wf(sc),
    ensures out@ == state@, runtime_image_view_wf(&out),
{
    let h = raw_create_image_view(ctx, image_handle, format, aspect);
    RuntimeImageView { handle: h, state: Ghost(state@) }
}

/// Destroy an image view.
/// Caller must prove device is idle and no live framebuffer references this view.
#[verifier::external_body]
pub fn vk_destroy_image_view(
    ctx: &VulkanContext,
    view: &mut RuntimeImageView,
    dev: &RuntimeDevice,
    // Ghost: caller attests no live framebuffer references this view
    no_live_framebuffers: Ghost<bool>,
)
    requires
        runtime_image_view_wf(&*old(view)),
        // Device must be idle
        forall|i: int| 0 <= i < dev@.pending_submissions.len()
            ==> (#[trigger] dev@.pending_submissions[i]).completed,
        // Caller attests no framebuffer references this view
        no_live_framebuffers@,
    ensures
        view@ == destroy_image_view_ghost(old(view)@),
        !view@.alive,
{
    raw_destroy_image_view(ctx, view.handle);
    view.state = Ghost(destroy_image_view_ghost(view.state@));
}

// ── Framebuffer FFI ──────────────────────────────────────────────────

/// Create a framebuffer.
/// Caller must prove the render pass is alive and the ghost state matches it.
#[verifier::external_body]
pub fn vk_create_framebuffer(
    ctx: &VulkanContext,
    state: Ghost<FramebufferState>,
    rp: &RuntimeRenderPass,
    view_handles: &[u64],
    w: u32,
    h: u32,
) -> (out: RuntimeFramebuffer)
    requires
        state@.alive,
        // Render pass must be alive
        runtime_render_pass_wf(rp),
        // Ghost state must reference this render pass
        state@.render_pass_id == rp@.id,
        // Attachment count must match render pass
        framebuffer_attachment_count_matches(state@, rp@),
    ensures out@ == state@, runtime_framebuffer_wf(&out),
{
    let handle = raw_create_framebuffer(ctx, rp.handle, view_handles, w, h);
    RuntimeFramebuffer { handle, state: Ghost(state@) }
}

/// Destroy a framebuffer.
/// Caller must prove device is idle.
#[verifier::external_body]
pub fn vk_destroy_framebuffer(
    ctx: &VulkanContext,
    fb: &mut RuntimeFramebuffer,
    dev: &RuntimeDevice,
)
    requires
        runtime_framebuffer_wf(&*old(fb)),
        // Device must be idle — framebuffer may be referenced by pending command buffers
        forall|i: int| 0 <= i < dev@.pending_submissions.len()
            ==> (#[trigger] dev@.pending_submissions[i]).completed,
    ensures
        fb@ == destroy_framebuffer_ghost(old(fb)@),
        !fb@.alive,
{
    raw_destroy_framebuffer(ctx, fb.handle);
    fb.state = Ghost(destroy_framebuffer_ghost(fb.state@));
}

// ── Command Pool FFI ─────────────────────────────────────────────────

/// Create a command pool.
#[verifier::external_body]
pub fn vk_create_command_pool(
    ctx: &VulkanContext,
    id: Ghost<nat>,
    queue_family: u32,
    individual_reset: bool,
) -> (out: RuntimeCommandPool)
    ensures
        out@ == create_command_pool(id@, queue_family as nat, individual_reset),
        runtime_command_pool_wf(&out),
        pool_empty(out@),
{
    let flags = if individual_reset {
        vk::CommandPoolCreateFlags::RESET_COMMAND_BUFFER.as_raw()
    } else {
        0u32
    };
    let h = raw_create_command_pool(ctx, queue_family, flags);
    proof { lemma_fresh_pool_well_formed(id@, queue_family as nat, individual_reset); }
    RuntimeCommandPool {
        handle: h,
        state: Ghost(create_command_pool(id@, queue_family as nat, individual_reset)),
    }
}

/// Destroy a command pool.
/// Caller must prove pool is empty and device is idle.
#[verifier::external_body]
pub fn vk_destroy_command_pool(
    ctx: &VulkanContext,
    pool: &mut RuntimeCommandPool,
    dev: &RuntimeDevice,
)
    requires
        runtime_command_pool_wf(&*old(pool)),
        pool_empty(old(pool)@),
        // Device must be idle — command buffers from this pool may be in-flight
        forall|i: int| 0 <= i < dev@.pending_submissions.len()
            ==> (#[trigger] dev@.pending_submissions[i]).completed,
    ensures
        pool@ == destroy_command_pool_ghost(old(pool)@),
        !pool@.alive,
{
    raw_destroy_command_pool(ctx, pool.handle);
    pool.state = Ghost(destroy_command_pool_ghost(pool.state@));
}

// ── Swapchain Image Query FFI ────────────────────────────────────────

/// Get swapchain image handles.
#[verifier::external_body]
pub fn vk_get_swapchain_images(
    ctx: &VulkanContext,
    sc: &RuntimeSwapchain,
) -> (out: Vec<u64>)
    requires runtime_swapchain_wf(sc),
    ensures out@.len() == sc@.image_states.len(),
{
    let handles = raw_get_swapchain_images(ctx, sc.handle);
    handles
}

// ── Graphics Pipeline FFI (hardened) ─────────────────────────────────

/// Create a graphics pipeline with full precondition checking.
///
/// Caller must prove:
/// - Render pass alive + pipeline compatible with its subpass
/// - Pipeline layout alive
/// - Both shader modules alive + correct stages
/// - Full shader-pipeline interface compatibility (vertex inputs, descriptor
///   bindings, push constants, fragment output count)
///
/// Ghost params `vertex_attributes` and `resolved_set_layouts` carry the
/// resolved data that the spec needs but isn't stored in the pipeline state
/// (GraphicsPipelineState only has layout IDs, not full layouts).
#[verifier::external_body]
pub fn vk_create_graphics_pipeline_checked(
    ctx: &VulkanContext,
    gps: Ghost<GraphicsPipelineState>,
    layout: &RuntimePipelineLayout,
    rp: &RuntimeRenderPass,
    vert: &RuntimeShaderModule,
    frag: &RuntimeShaderModule,
    // Ghost: the vertex attributes the pipeline's vertex input state provides
    vertex_attributes: Ghost<Seq<ShaderInputAttribute>>,
    // Ghost: resolved descriptor set layouts (full objects, not just IDs)
    resolved_set_layouts: Ghost<Seq<DescriptorSetLayoutState>>,
) -> (out: RuntimeGraphicsPipeline)
    requires
        gps@.alive,
        // Render pass must be alive
        runtime_render_pass_wf(rp),
        // Pipeline must be compatible with the render pass subpass
        graphics_pipeline_compatible_with_subpass(gps@, rp@, gps@.subpass_index),
        // Pipeline layout must be alive
        runtime_pipeline_layout_wf(layout),
        // Shader modules must be alive
        runtime_shader_module_wf(vert),
        runtime_shader_module_wf(frag),
        // Shader stages must be correct
        shader_module_is_vertex(vert@),
        shader_module_is_fragment(frag@),
        // Resolved layouts must correspond to the pipeline layout's set_layout IDs
        resolved_set_layouts@.len() == layout@.set_layouts.len(),
        forall|i: int| 0 <= i < resolved_set_layouts@.len() ==>
            (#[trigger] resolved_set_layouts@[i]).id == layout@.set_layouts[i]
            && resolved_set_layouts@[i].alive,
        // Full shader-pipeline interface compatibility
        shader_pipeline_compatible(
            vert@.interface,
            frag@.interface,
            vertex_attributes@,
            resolved_set_layouts@,
            layout@.push_constant_ranges,
            gps@.color_attachment_count,
        ),
    ensures
        out@ == gps@,
        runtime_gfx_pipeline_wf(&out),
{
    let h = raw_create_graphics_pipeline(ctx, layout.handle, rp.handle, vert.handle, frag.handle);
    RuntimeGraphicsPipeline { handle: h, state: Ghost(gps@) }
}

} // verus!
