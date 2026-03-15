//! Verified-FFI triangle demo.
//!
//! Run with Vulkan:  `cargo run --bin triangle --features vulkan-backend`
//! Run with WebGPU:  `cargo run --bin triangle --features webgpu-backend`

#[cfg(all(feature = "vulkan-backend", feature = "webgpu-backend"))]
compile_error!("Enable only one of `vulkan-backend` or `webgpu-backend`, not both.");

use winit::{
    application::ApplicationHandler,
    event::WindowEvent,
    event_loop::{ActiveEventLoop, EventLoop},
    window::{Window, WindowId, WindowAttributes},
};

// ═══════════════════════════════════════════════════════════════════════════
// WebGPU backend
// ═══════════════════════════════════════════════════════════════════════════

#[cfg(feature = "webgpu-backend")]
mod webgpu {
    use super::*;
    use std::sync::Arc;

    pub struct GpuState {
        pub surface: wgpu::Surface<'static>,
        pub device: wgpu::Device,
        pub queue: wgpu::Queue,
        pub config: wgpu::SurfaceConfiguration,
        pub pipeline: wgpu::RenderPipeline,
    }

    impl GpuState {
        pub async fn new(window: Arc<Window>) -> Self {
            let size = window.inner_size();
            let instance = wgpu::Instance::new(&wgpu::InstanceDescriptor {
                backends: wgpu::Backends::all(),
                ..Default::default()
            });
            let surface = instance.create_surface(window).unwrap();
            let adapter = instance
                .request_adapter(&wgpu::RequestAdapterOptions {
                    compatible_surface: Some(&surface),
                    ..Default::default()
                })
                .await
                .expect("No suitable GPU adapter");
            let (device, queue) = adapter
                .request_device(&wgpu::DeviceDescriptor::default(), None)
                .await
                .expect("Failed to create device");

            let caps = surface.get_capabilities(&adapter);
            let format = caps.formats[0];
            let config = wgpu::SurfaceConfiguration {
                usage: wgpu::TextureUsages::RENDER_ATTACHMENT,
                format,
                width: size.width.max(1),
                height: size.height.max(1),
                present_mode: wgpu::PresentMode::Fifo,
                alpha_mode: caps.alpha_modes[0],
                view_formats: vec![],
                desired_maximum_frame_latency: 2,
            };
            surface.configure(&device, &config);

            let shader = device.create_shader_module(wgpu::ShaderModuleDescriptor {
                label: Some("triangle"),
                source: wgpu::ShaderSource::Wgsl(
                    include_str!("shaders/triangle.wgsl").into(),
                ),
            });

            let layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
                label: None,
                bind_group_layouts: &[],
                push_constant_ranges: &[],
            });

            let pipeline = device.create_render_pipeline(&wgpu::RenderPipelineDescriptor {
                label: Some("triangle"),
                layout: Some(&layout),
                vertex: wgpu::VertexState {
                    module: &shader,
                    entry_point: Some("vs_main"),
                    buffers: &[],
                    compilation_options: Default::default(),
                },
                fragment: Some(wgpu::FragmentState {
                    module: &shader,
                    entry_point: Some("fs_main"),
                    targets: &[Some(wgpu::ColorTargetState {
                        format,
                        blend: Some(wgpu::BlendState::REPLACE),
                        write_mask: wgpu::ColorWrites::ALL,
                    })],
                    compilation_options: Default::default(),
                }),
                primitive: wgpu::PrimitiveState {
                    topology: wgpu::PrimitiveTopology::TriangleList,
                    ..Default::default()
                },
                depth_stencil: None,
                multisample: wgpu::MultisampleState::default(),
                multiview: None,
                cache: None,
            });

            GpuState { surface, device, queue, config, pipeline }
        }

        pub fn resize(&mut self, width: u32, height: u32) {
            if width > 0 && height > 0 {
                self.config.width = width;
                self.config.height = height;
                self.surface.configure(&self.device, &self.config);
            }
        }

        pub fn render(&self) -> Result<(), wgpu::SurfaceError> {
            let frame = self.surface.get_current_texture()?;
            let view = frame.texture.create_view(&Default::default());
            let mut encoder = self.device.create_command_encoder(&Default::default());
            {
                let mut pass = encoder.begin_render_pass(&wgpu::RenderPassDescriptor {
                    label: Some("triangle"),
                    color_attachments: &[Some(wgpu::RenderPassColorAttachment {
                        view: &view,
                        resolve_target: None,
                        ops: wgpu::Operations {
                            load: wgpu::LoadOp::Clear(wgpu::Color {
                                r: 0.1, g: 0.1, b: 0.1, a: 1.0,
                            }),
                            store: wgpu::StoreOp::Store,
                        },
                    })],
                    depth_stencil_attachment: None,
                    ..Default::default()
                });
                pass.set_pipeline(&self.pipeline);
                pass.draw(0..3, 0..1);
            }
            self.queue.submit(std::iter::once(encoder.finish()));
            frame.present();
            Ok(())
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// Vulkan backend — uses verified FFI for all Vulkan object management
// ═══════════════════════════════════════════════════════════════════════════

#[cfg(feature = "vulkan-backend")]
mod vulkan {
    use super::*;
    use std::sync::Arc;
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
    }

    impl VkState {
        pub fn new(window: Arc<Window>) -> Self {
            let size = window.inner_size();
            let width = size.width.max(1);
            let height = size.height.max(1);

            // 1. Required surface extensions from the windowing system
            let display_handle = window.display_handle().unwrap();
            let surface_extensions =
                ash_window::enumerate_required_extensions(display_handle.as_raw())
                    .expect("Failed to get required surface extensions");

            // Device extensions: swapchain (portability subset auto-added by VulkanContext on macOS)
            let device_exts: Vec<*const i8> = vec![ash::khr::swapchain::NAME.as_ptr()];

            // 2. Create VulkanContext (instance + device + loaders)
            let ctx = unsafe {
                VulkanContext::new("triangle", true, surface_extensions, &device_exts, 0)
            };

            // 3. Create surface via ash-window, then wrap with verified FFI
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

            // 4. Create RuntimeDevice wrapper (ghost state for destroy preconditions)
            let dev = ffi::vk_create_device(&ctx, Ghost::assume_new());

            // 5. Get graphics queue
            let queue = ffi::vk_get_device_queue(&ctx, 0, 0, Ghost::assume_new());

            // 6. Query surface format
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

            // 7. Create swapchain (double-buffered, FIFO)
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
            );

            // 8. Get swapchain images → create image views
            let images = ffi::vk_get_swapchain_images(&ctx, &swapchain);
            let mut image_views = Vec::new();
            for &img in images.iter() {
                let view = ffi::vk_create_image_view(
                    &ctx,
                    Ghost::assume_new(),
                    &swapchain,
                    img,
                    format.as_raw() as u32,
                    vk::ImageAspectFlags::COLOR.as_raw() as u32,
                );
                image_views.push(view);
            }

            // 9. Create render pass (single color attachment, clear on load, store)
            let render_pass = ffi::vk_create_render_pass(
                &ctx,
                Ghost::assume_new(),
                format.as_raw() as u32,
                vk::AttachmentLoadOp::CLEAR.as_raw() as u32,
                vk::AttachmentStoreOp::STORE.as_raw() as u32,
                vk::SampleCountFlags::TYPE_1.as_raw() as u32,
            );

            // 10. Create framebuffers (one per swapchain image)
            let mut framebuffers = Vec::new();
            for view in &image_views {
                let fb = ffi::vk_create_framebuffer(
                    &ctx,
                    Ghost::assume_new(),
                    &render_pass,
                    &[view.handle],
                    width,
                    height,
                );
                framebuffers.push(fb);
            }

            // 11. Create shader modules from pre-compiled SPIR-V
            let vert_code = spv_to_u32(include_bytes!("shaders/triangle.vert.spv"));
            let vert_module = ffi::vk_create_shader_module(&ctx, Ghost::assume_new(), &vert_code);

            let frag_code = spv_to_u32(include_bytes!("shaders/triangle.frag.spv"));
            let frag_module = ffi::vk_create_shader_module(&ctx, Ghost::assume_new(), &frag_code);

            // 12. Create pipeline layout (no descriptors, no push constants)
            let pipeline_layout_handle = ffi::vk_create_pipeline_layout(&ctx, &[]);

            // 13. Create graphics pipeline
            let pipeline = ffi::vk_create_graphics_pipeline(
                &ctx,
                Ghost::assume_new(),
                pipeline_layout_handle,
                render_pass.handle,
                vert_module.handle,
                frag_module.handle,
            );

            // 14. Create command pool + one command buffer per swapchain image
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

            // 15. Create sync objects
            let in_flight_fence = ffi::vk_create_fence(&ctx, Ghost::assume_new(), true);
            let image_available_sem = ffi::vk_create_semaphore(&ctx, Ghost::assume_new());
            let render_finished_sem = ffi::vk_create_semaphore(&ctx, Ghost::assume_new());

            eprintln!("Vulkan backend initialized: {}x{}, format {:?}", width, height, format);

            VkState {
                ctx, dev, raw_surface, surface, queue, swapchain, image_views,
                render_pass, framebuffers, pipeline, pipeline_layout_handle,
                command_pool, command_buffers, image_available_sem,
                render_finished_sem, in_flight_fence, vert_module, frag_module,
                format, width, height,
            }
        }

        pub fn resize(&mut self, width: u32, height: u32) {
            if width == 0 || height == 0 {
                return;
            }
            self.width = width;
            self.height = height;
            // TODO: recreate swapchain + framebuffers for resize
        }

        pub fn render(&mut self) {
            // Wait for previous frame to finish
            ffi::vk_wait_for_fences(
                &self.ctx, &mut self.in_flight_fence, Ghost::assume_new(), u64::MAX,
            );
            ffi::vk_reset_fences(&self.ctx, &mut self.in_flight_fence);

            // Acquire next swapchain image
            let idx = ffi::vk_acquire_next_image(
                &self.ctx,
                &mut self.swapchain,
                self.image_available_sem.handle,
                0, // no fence for acquire
                u64::MAX,
            );

            let cb = &mut self.command_buffers[idx as usize];

            // Record commands
            ffi::vk_begin_command_buffer(&self.ctx, cb);
            ffi::vk_cmd_begin_render_pass(
                &self.ctx,
                cb,
                self.render_pass.handle,
                self.framebuffers[idx as usize].handle,
                self.width,
                self.height,
                0.1, 0.1, 0.1, 1.0, // clear color
            );
            ffi::vk_cmd_bind_pipeline(
                &self.ctx,
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
            ffi::vk_cmd_draw(&self.ctx, cb, 3, 1, 0, 0);
            ffi::vk_cmd_end_render_pass(&self.ctx, cb);
            ffi::vk_end_command_buffer(&self.ctx, cb);

            // Submit
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

            // Present
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

// ═══════════════════════════════════════════════════════════════════════════
// Application handler
// ═══════════════════════════════════════════════════════════════════════════

enum Backend {
    #[cfg(feature = "webgpu-backend")]
    WebGpu(webgpu::GpuState),
    #[cfg(feature = "vulkan-backend")]
    Vulkan(vulkan::VkState),
    None,
}

struct App {
    window: Option<std::sync::Arc<Window>>,
    backend: Backend,
}

impl ApplicationHandler for App {
    fn resumed(&mut self, event_loop: &ActiveEventLoop) {
        if self.window.is_some() {
            return;
        }
        let attrs = WindowAttributes::default().with_title("Verified Triangle");
        let window = std::sync::Arc::new(
            event_loop.create_window(attrs).expect("Failed to create window"),
        );
        self.window = Some(window.clone());

        #[cfg(feature = "webgpu-backend")]
        {
            let gpu = pollster::block_on(webgpu::GpuState::new(window));
            self.backend = Backend::WebGpu(gpu);
            return;
        }

        #[cfg(feature = "vulkan-backend")]
        {
            let vk = vulkan::VkState::new(window.clone());
            self.backend = Backend::Vulkan(vk);
            window.request_redraw();
            return;
        }

        #[allow(unreachable_code)]
        {
            eprintln!("No backend enabled! Use --features vulkan-backend or --features webgpu-backend");
            event_loop.exit();
        }
    }

    fn window_event(&mut self, event_loop: &ActiveEventLoop, _id: WindowId, event: WindowEvent) {
        match event {
            WindowEvent::CloseRequested => {
                #[cfg(feature = "vulkan-backend")]
                if let Backend::Vulkan(ref mut vk) = self.backend {
                    vk.destroy();
                }
                event_loop.exit();
            }
            WindowEvent::Resized(size) => {
                match &mut self.backend {
                    #[cfg(feature = "webgpu-backend")]
                    Backend::WebGpu(gpu) => gpu.resize(size.width, size.height),
                    #[cfg(feature = "vulkan-backend")]
                    Backend::Vulkan(vk) => vk.resize(size.width, size.height),
                    _ => {}
                }
            }
            WindowEvent::RedrawRequested => {
                match &mut self.backend {
                    #[cfg(feature = "webgpu-backend")]
                    Backend::WebGpu(gpu) => {
                        match gpu.render() {
                            Ok(_) => {}
                            Err(wgpu::SurfaceError::Lost) => {
                                // Reconfigure on next frame
                            }
                            Err(e) => eprintln!("Render error: {e:?}"),
                        }
                    }
                    #[cfg(feature = "vulkan-backend")]
                    Backend::Vulkan(vk) => vk.render(),
                    _ => {}
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
        backend: Backend::None,
    };
    event_loop.run_app(&mut app).expect("Event loop error");
}
