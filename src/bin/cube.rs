//! Spinning cube demo with depth testing + push constants.
//!
//! Run: `cargo run --bin cube --features vulkan-backend`

use winit::{
    application::ApplicationHandler,
    event::WindowEvent,
    event_loop::{ActiveEventLoop, EventLoop},
    window::{Window, WindowId, WindowAttributes},
};

//  ═══════════════════════════════════════════════════════════════════════════
//  Matrix math — simple [f32; 16] column-major helpers
//  ═══════════════════════════════════════════════════════════════════════════

fn mat4_identity() -> [f32; 16] {
    [
        1.0, 0.0, 0.0, 0.0,
        0.0, 1.0, 0.0, 0.0,
        0.0, 0.0, 1.0, 0.0,
        0.0, 0.0, 0.0, 1.0,
    ]
}

fn mat4_perspective(fov_y: f32, aspect: f32, near: f32, far: f32) -> [f32; 16] {
    let f = 1.0 / (fov_y / 2.0).tan();
    let nf = 1.0 / (near - far);
    [
        f / aspect, 0.0, 0.0,              0.0,
        0.0,        -f,  0.0,              0.0,
        0.0,        0.0, far * nf,         -1.0,
        0.0,        0.0, near * far * nf,  0.0,
    ]
}

fn mat4_translate(x: f32, y: f32, z: f32) -> [f32; 16] {
    [
        1.0, 0.0, 0.0, 0.0,
        0.0, 1.0, 0.0, 0.0,
        0.0, 0.0, 1.0, 0.0,
        x,   y,   z,   1.0,
    ]
}

fn mat4_rotate_y(angle: f32) -> [f32; 16] {
    let c = angle.cos();
    let s = angle.sin();
    [
        c,   0.0, -s,  0.0,
        0.0, 1.0, 0.0, 0.0,
        s,   0.0, c,   0.0,
        0.0, 0.0, 0.0, 1.0,
    ]
}

fn mat4_rotate_x(angle: f32) -> [f32; 16] {
    let c = angle.cos();
    let s = angle.sin();
    [
        1.0, 0.0, 0.0, 0.0,
        0.0, c,   s,   0.0,
        0.0, -s,  c,   0.0,
        0.0, 0.0, 0.0, 1.0,
    ]
}

fn mat4_mul(a: &[f32; 16], b: &[f32; 16]) -> [f32; 16] {
    let mut out = [0.0f32; 16];
    for c in 0..4 {
        for r in 0..4 {
            out[c * 4 + r] = a[0 * 4 + r] * b[c * 4 + 0]
                           + a[1 * 4 + r] * b[c * 4 + 1]
                           + a[2 * 4 + r] * b[c * 4 + 2]
                           + a[3 * 4 + r] * b[c * 4 + 3];
        }
    }
    out
}

//  ═══════════════════════════════════════════════════════════════════════════
//  Vulkan backend
//  ═══════════════════════════════════════════════════════════════════════════

mod vulkan {
    use super::*;
    use std::sync::Arc;
    use std::time::Instant;
    use ash::vk;
    use ash::vk::Handle;
    use builtin::Ghost;
    use raw_window_handle::{HasDisplayHandle, HasWindowHandle};
    use verus_vulkan::vk_context::VulkanContext;
    use verus_vulkan::ffi;
    use verus_vulkan::runtime::surface::RuntimeSurface;
    use verus_vulkan::runtime::swapchain::RuntimeSwapchain;
    use verus_vulkan::runtime::shader_module::RuntimeShaderModule;
    use verus_vulkan::runtime::render_pass::RuntimeRenderPass;
    use verus_vulkan::runtime::framebuffer::{RuntimeFramebuffer, RuntimeImageView};
    use verus_vulkan::runtime::command_pool::RuntimeCommandPool;
    use verus_vulkan::runtime::command_buffer::RuntimeCommandBuffer;
    use verus_vulkan::runtime::fence::RuntimeFence;
    use verus_vulkan::runtime::semaphore::RuntimeSemaphore;
    use verus_vulkan::runtime::device::RuntimeDevice;
    use verus_vulkan::runtime::queue::RuntimeQueue;
    use verus_vulkan::runtime::pipeline::RuntimeGraphicsPipeline;
    use verus_vulkan::runtime::image::RuntimeImage;

    pub struct VkState {
        ctx: VulkanContext,
        dev: RuntimeDevice,
        raw_surface: vk::SurfaceKHR,
        surface: RuntimeSurface,
        queue: RuntimeQueue,
        swapchain: RuntimeSwapchain,
        image_views: Vec<RuntimeImageView>,
        render_pass: RuntimeRenderPass,
        framebuffers: Vec<RuntimeFramebuffer>,
        pipeline: RuntimeGraphicsPipeline,
        pipeline_layout_handle: u64,
        command_pool: RuntimeCommandPool,
        command_buffers: Vec<RuntimeCommandBuffer>,
        image_available_sem: RuntimeSemaphore,
        render_finished_sem: RuntimeSemaphore,
        in_flight_fence: RuntimeFence,
        vert_module: RuntimeShaderModule,
        frag_module: RuntimeShaderModule,
        format: vk::Format,
        width: u32,
        height: u32,
        //  Depth buffer
        depth_image: RuntimeImage,
        depth_memory: vk::DeviceMemory,
        depth_view: RuntimeImageView,
        //  Animation
        start_time: Instant,
    }

    fn find_memory_type(
        instance: &ash::Instance,
        pdev: vk::PhysicalDevice,
        type_filter: u32,
        properties: vk::MemoryPropertyFlags,
    ) -> u32 {
        let mem_props = unsafe { instance.get_physical_device_memory_properties(pdev) };
        for i in 0..mem_props.memory_type_count {
            if (type_filter & (1 << i)) != 0
                && mem_props.memory_types[i as usize]
                    .property_flags
                    .contains(properties)
            {
                return i;
            }
        }
        panic!("Failed to find suitable memory type");
    }

    impl VkState {
        pub fn new(window: Arc<Window>) -> Self {
            let size = window.inner_size();
            let width = size.width.max(1);
            let height = size.height.max(1);

            //  1. Required surface extensions
            let display_handle = window.display_handle().unwrap();
            let surface_extensions =
                ash_window::enumerate_required_extensions(display_handle.as_raw())
                    .expect("Failed to get required surface extensions");

            let device_exts: Vec<*const i8> = vec![ash::khr::swapchain::NAME.as_ptr()];

            //  2. Create VulkanContext
            let ctx = unsafe {
                VulkanContext::new("cube", true, surface_extensions, &device_exts, 0)
            };

            //  3. Create surface
            let raw_surface = unsafe {
                ash_window::create_surface(
                    &ctx.entry,
                    &ctx.instance,
                    display_handle.as_raw(),
                    window.window_handle().unwrap().as_raw(),
                    None,
                )
            }
            .expect("Failed to create Vulkan surface");
            let surface = ffi::vk_create_surface(&ctx, Ghost::assume_new(), raw_surface.as_raw());

            //  4. Device + queue
            let mut dev = ffi::vk_create_device(&ctx, Ghost::assume_new());
            let queue = ffi::vk_get_device_queue(&ctx, 0, 0, Ghost::assume_new());

            //  5. Surface format
            let surface_formats = unsafe {
                ctx.surface_loader
                    .get_physical_device_surface_formats(ctx.physical_device, raw_surface)
            }
            .expect("Failed to query surface formats");
            let format = surface_formats
                .iter()
                .find(|f| f.format == vk::Format::B8G8R8A8_SRGB)
                .unwrap_or(&surface_formats[0])
                .format;

            //  6. Swapchain
            let image_count = 2u64;
            let swapchain = ffi::vk_create_swapchain(
                &ctx,
                Ghost::assume_new(),
                image_count,
                raw_surface.as_raw(),
                format.as_raw() as u32,
                width,
                height,
                vk::PresentModeKHR::FIFO.as_raw() as u32,
                vk::ImageUsageFlags::COLOR_ATTACHMENT.as_raw(),
            );

            //  7. Swapchain image views
            let images = ffi::vk_get_swapchain_images(&ctx, &swapchain);
            let mut image_views = Vec::new();
            for &img in images.iter() {
                let view = ffi::vk_create_image_view(
                    &ctx,
                    Ghost::assume_new(),
                    img,
                    format.as_raw() as u32,
                    vk::ImageAspectFlags::COLOR.as_raw() as u32,
                );
                image_views.push(view);
            }

            //  8. Depth buffer
            let depth_format = vk::Format::D32_SFLOAT;
            let depth_image = ffi::vk_create_image(
                &ctx,
                &mut dev,
                Ghost::assume_new(),
                width, height, 1,
                depth_format.as_raw() as u32,
                1, 1,
                vk::SampleCountFlags::TYPE_1.as_raw() as u32,
                vk::ImageTiling::OPTIMAL.as_raw() as u32,
                vk::ImageUsageFlags::DEPTH_STENCIL_ATTACHMENT.as_raw() as u32,
            );
            let mem_reqs = unsafe { ctx.device.get_image_memory_requirements(vk::Image::from_raw(depth_image.handle)) };
            let mem_type_idx = find_memory_type(
                &ctx.instance,
                ctx.physical_device,
                mem_reqs.memory_type_bits,
                vk::MemoryPropertyFlags::DEVICE_LOCAL,
            );
            let alloc_info = vk::MemoryAllocateInfo::default()
                .allocation_size(mem_reqs.size)
                .memory_type_index(mem_type_idx);
            let depth_memory =
                unsafe { ctx.device.allocate_memory(&alloc_info, None) }
                    .expect("Failed to allocate depth buffer memory");
            unsafe { ctx.device.bind_image_memory(vk::Image::from_raw(depth_image.handle), depth_memory, 0) }
                .expect("Failed to bind depth image memory");
            let depth_view = ffi::vk_create_image_view(
                &ctx,
                Ghost::assume_new(),
                depth_image.handle,
                depth_format.as_raw() as u32,
                vk::ImageAspectFlags::DEPTH.as_raw() as u32,
            );

            //  9. Render pass (color + depth)
            let render_pass = ffi::vk_create_render_pass_depth(
                &ctx,
                Ghost::assume_new(),
                format.as_raw() as u32,
                depth_format.as_raw() as u32,
                vk::AttachmentLoadOp::CLEAR.as_raw() as u32,
                vk::AttachmentStoreOp::STORE.as_raw() as u32,
                vk::SampleCountFlags::TYPE_1.as_raw() as u32,
            );

            //  10. Framebuffers (color view + depth view per swapchain image)
            let mut framebuffers = Vec::new();
            for view in &image_views {
                let fb = ffi::vk_create_framebuffer(
                    &ctx,
                    Ghost::assume_new(),
                    &render_pass,
                    &[view.handle, depth_view.handle],
                    width,
                    height,
                );
                framebuffers.push(fb);
            }

            //  11. Shader modules
            let vert_code = spv_to_u32(include_bytes!("shaders/cube.vert.spv"));
            let vert_module = ffi::vk_create_shader_module(&ctx, Ghost::assume_new(), &vert_code);

            let frag_code = spv_to_u32(include_bytes!("shaders/cube.frag.spv"));
            let frag_module = ffi::vk_create_shader_module(&ctx, Ghost::assume_new(), &frag_code);

            //  12. Pipeline layout with push constant (mat4 = 64 bytes at VERTEX stage)
            let pipeline_layout_handle = ffi::vk_create_pipeline_layout_push(
                &ctx,
                &[],
                vk::ShaderStageFlags::VERTEX.as_raw(),
                0,
                64, //  sizeof(mat4)
            );

            //  13. Graphics pipeline (depth test + back-face cull)
            let pipeline = ffi::vk_create_graphics_pipeline(
                &ctx,
                Ghost::assume_new(),
                pipeline_layout_handle,
                render_pass.handle,
                vert_module.handle,
                frag_module.handle,
                vk::CullModeFlags::BACK.as_raw(),
                vk::FrontFace::COUNTER_CLOCKWISE.as_raw() as u32,
                true, true,
                vk::CompareOp::LESS_OR_EQUAL.as_raw() as u32,
            );

            //  14. Command pool + buffers
            let command_pool = ffi::vk_create_command_pool(&ctx, Ghost::assume_new(), 0, true);
            let mut command_buffers = Vec::new();
            for _ in 0..image_count {
                let cb = ffi::vk_allocate_command_buffer(
                    &ctx,
                    Ghost::assume_new(),
                    command_pool.handle,
                );
                command_buffers.push(cb);
            }

            //  15. Sync objects
            let in_flight_fence = ffi::vk_create_fence(&ctx, Ghost::assume_new(), true);
            let image_available_sem = ffi::vk_create_semaphore(&ctx, Ghost::assume_new());
            let render_finished_sem = ffi::vk_create_semaphore(&ctx, Ghost::assume_new());

            eprintln!("Vulkan cube initialized: {}x{}, format {:?}", width, height, format);

            VkState {
                ctx, dev, raw_surface, surface, queue, swapchain, image_views,
                render_pass, framebuffers, pipeline, pipeline_layout_handle,
                command_pool, command_buffers, image_available_sem,
                render_finished_sem, in_flight_fence, vert_module, frag_module,
                format, width, height,
                depth_image, depth_memory, depth_view,
                start_time: Instant::now(),
            }
        }

        pub fn resize(&mut self, width: u32, height: u32) {
            if width == 0 || height == 0 {
                return;
            }
            self.width = width;
            self.height = height;
            //  TODO: recreate swapchain + framebuffers + depth buffer for resize
        }

        pub fn render(&mut self) {
            //  Wait for previous frame
            ffi::vk_wait_for_fences(
                &self.ctx, &mut self.in_flight_fence, Ghost::assume_new(), u64::MAX,
            );
            ffi::vk_reset_fences(&self.ctx, &mut self.in_flight_fence);

            //  Acquire next image
            let idx = ffi::vk_acquire_next_image(
                &self.ctx,
                &mut self.swapchain,
                self.image_available_sem.handle,
                0,
                u64::MAX,
            );

            let cb = &mut self.command_buffers[idx as usize];

            //  Compute MVP
            let elapsed = self.start_time.elapsed().as_secs_f32();
            let aspect = self.width as f32 / self.height as f32;
            let proj = mat4_perspective(std::f32::consts::FRAC_PI_4, aspect, 0.1, 100.0);
            let view = mat4_translate(0.0, 0.0, -3.0);
            let model = mat4_mul(&mat4_rotate_y(elapsed * 1.0), &mat4_rotate_x(elapsed * 0.5));
            let mvp = mat4_mul(&proj, &mat4_mul(&view, &model));
            let mvp_bytes: &[u8] = unsafe {
                std::slice::from_raw_parts(mvp.as_ptr() as *const u8, 64)
            };

            //  Record commands
            ffi::vk_begin_command_buffer(&self.ctx, cb);
            ffi::vk_cmd_begin_render_pass_depth(
                &self.ctx,
                Ghost::assume_new(),
                Ghost::assume_new(),
                cb,
                self.render_pass.handle,
                self.framebuffers[idx as usize].handle,
                self.width,
                self.height,
                0.1, 0.1, 0.1, 1.0, //  clear color
                1.0, 0,              //  clear depth/stencil
            );
            ffi::vk_cmd_bind_pipeline(
                &self.ctx,
                Ghost::assume_new(),
                Ghost::assume_new(),
                cb,
                vk::PipelineBindPoint::GRAPHICS.as_raw() as u32,
                self.pipeline.handle,
            );
            ffi::ffi_cmd_set_viewport(
                &self.ctx,
                cb.handle,
                0.0, 0.0, self.width as f32, self.height as f32, 0.0, 1.0,
            );
            ffi::ffi_cmd_set_scissor(
                &self.ctx,
                cb.handle,
                0, 0, self.width, self.height,
            );
            ffi::ffi_cmd_push_constants(
                &self.ctx,
                cb.handle,
                self.pipeline_layout_handle,
                vk::ShaderStageFlags::VERTEX.as_raw(),
                0,
                mvp_bytes,
            );
            ffi::vk_cmd_draw(&self.ctx, cb, 36, 1, 0, 0); //  36 vertices = 12 triangles
            ffi::vk_cmd_end_render_pass(&self.ctx, cb);
            ffi::vk_end_command_buffer(&self.ctx, cb);

            //  Submit
            let wait_stage = vk::PipelineStageFlags::COLOR_ATTACHMENT_OUTPUT.as_raw();
            ffi::vk_queue_submit(
                &self.ctx,
                &self.queue,
                Ghost::assume_new(),
                Ghost::assume_new(),
                Ghost::assume_new(),
                &[cb.handle],
                &[self.image_available_sem.handle],
                &[wait_stage],
                &[self.render_finished_sem.handle],
                self.in_flight_fence.handle,
            );

            //  Present
            ffi::vk_queue_present_khr(
                &self.ctx,
                &self.queue,
                &mut self.swapchain,
                idx,
                &[self.render_finished_sem.handle],
            );
        }

        pub fn destroy(&mut self) {
            unsafe {
                let _ = self.ctx.device.device_wait_idle();
                self.ctx.device.destroy_pipeline(vk::Pipeline::from_raw(self.pipeline.handle), None);
                self.ctx.device.destroy_pipeline_layout(vk::PipelineLayout::from_raw(self.pipeline_layout_handle), None);
                self.ctx.device.destroy_shader_module(vk::ShaderModule::from_raw(self.vert_module.handle), None);
                self.ctx.device.destroy_shader_module(vk::ShaderModule::from_raw(self.frag_module.handle), None);
                for fb in &self.framebuffers {
                    self.ctx.device.destroy_framebuffer(vk::Framebuffer::from_raw(fb.handle), None);
                }
                for iv in &self.image_views {
                    self.ctx.device.destroy_image_view(vk::ImageView::from_raw(iv.handle), None);
                }
                //  Depth buffer cleanup
                self.ctx.device.destroy_image_view(vk::ImageView::from_raw(self.depth_view.handle), None);
                self.ctx.device.destroy_image(vk::Image::from_raw(self.depth_image.handle), None);
                self.ctx.device.free_memory(self.depth_memory, None);
                self.ctx.device.destroy_render_pass(vk::RenderPass::from_raw(self.render_pass.handle), None);
                self.ctx.device.destroy_command_pool(vk::CommandPool::from_raw(self.command_pool.handle), None);
                self.ctx.device.destroy_fence(vk::Fence::from_raw(self.in_flight_fence.handle), None);
                self.ctx.device.destroy_semaphore(vk::Semaphore::from_raw(self.image_available_sem.handle), None);
                self.ctx.device.destroy_semaphore(vk::Semaphore::from_raw(self.render_finished_sem.handle), None);
                self.ctx.swapchain_loader.destroy_swapchain(vk::SwapchainKHR::from_raw(self.swapchain.handle), None);
                self.ctx.surface_loader.destroy_surface(self.raw_surface, None);
                self.ctx.destroy();
            }
        }
    }

    fn spv_to_u32(bytes: &[u8]) -> Vec<u32> {
        bytes
            .chunks_exact(4)
            .map(|c| u32::from_le_bytes([c[0], c[1], c[2], c[3]]))
            .collect()
    }
}

//  ═══════════════════════════════════════════════════════════════════════════
//  Application handler
//  ═══════════════════════════════════════════════════════════════════════════

struct App {
    window: Option<std::sync::Arc<Window>>,
    state: Option<vulkan::VkState>,
}

impl ApplicationHandler for App {
    fn resumed(&mut self, event_loop: &ActiveEventLoop) {
        if self.window.is_some() {
            return;
        }
        let attrs = WindowAttributes::default().with_title("Verified Spinning Cube");
        let window = std::sync::Arc::new(
            event_loop.create_window(attrs).expect("Failed to create window"),
        );
        self.window = Some(window.clone());
        self.state = Some(vulkan::VkState::new(window.clone()));
        window.request_redraw();
    }

    fn window_event(&mut self, event_loop: &ActiveEventLoop, _id: WindowId, event: WindowEvent) {
        match event {
            WindowEvent::CloseRequested => {
                event_loop.exit();
            }
            WindowEvent::Resized(size) => {
                if let Some(ref mut vk) = self.state {
                    vk.resize(size.width, size.height);
                }
            }
            WindowEvent::RedrawRequested => {
                if let Some(ref mut vk) = self.state {
                    vk.render();
                }
                if let Some(w) = &self.window {
                    w.request_redraw();
                }
            }
            _ => {}
        }
    }
}

fn main() {
    let event_loop = EventLoop::new().expect("Failed to create event loop");
    let mut app = App {
        window: None,
        state: None,
    };
    let _ = event_loop.run_app(&mut app);
    if let Some(ref mut vk) = app.state {
        vk.destroy();
    }
}
