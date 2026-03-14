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
// Vulkan backend (placeholder — needs compiled SPIR-V)
// ═══════════════════════════════════════════════════════════════════════════

#[cfg(feature = "vulkan-backend")]
mod vulkan {
    use super::*;
    use std::sync::Arc;
    use ash::vk;
    use verus_vulkan::vk_context::VulkanContext;

    pub struct VkState {
        pub ctx: VulkanContext,
        // TODO: fill in once SPIR-V shaders are compiled
    }

    impl VkState {
        pub fn new(window: Arc<Window>) -> Self {
            let surface_extensions =
                ash_window::enumerate_required_extensions(window.display_handle().unwrap().as_raw())
                    .expect("Failed to get required surface extensions");
            let device_extensions = [ash::khr::swapchain::NAME.as_ptr()];

            let ctx = unsafe {
                VulkanContext::new(
                    "triangle",
                    true,
                    surface_extensions,
                    &device_extensions,
                    0,
                )
            };

            // Create surface
            let _surface = unsafe {
                ash_window::create_surface(
                    &ctx.entry,
                    &ctx.instance,
                    window.display_handle().unwrap().as_raw(),
                    window.window_handle().unwrap().as_raw(),
                    None,
                )
            }
            .expect("Failed to create Vulkan surface");

            // TODO: swapchain, render pass, framebuffers, pipeline, command buffers, sync, frame loop
            eprintln!("Vulkan backend: surface created. Full pipeline TBD (need compiled SPIR-V).");

            VkState { ctx }
        }

        pub fn resize(&mut self, _width: u32, _height: u32) {
            // TODO: recreate swapchain
        }

        pub fn render(&self) {
            // TODO: acquire → record → submit → present
        }

        pub fn destroy(&mut self) {
            unsafe { self.ctx.destroy(); }
        }
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
            let vk = vulkan::VkState::new(window);
            self.backend = Backend::Vulkan(vk);
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
                match &self.backend {
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
