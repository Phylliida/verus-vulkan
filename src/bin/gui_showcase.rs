//! GUI Widget Showcase — demonstrates every verus-gui widget type
//! rendered via verus-vulkan's verified Vulkan FFI.
//!
//! Run: `./run.sh verus-vulkan --features gui-showcase --bin gui_showcase`

use winit::{
    application::ApplicationHandler,
    event::WindowEvent,
    event_loop::{ActiveEventLoop, EventLoop},
    window::{Window, WindowId, WindowAttributes},
};

// ═══════════════════════════════════════════════════════════════════════════
// Rational → f32 conversion
// ═══════════════════════════════════════════════════════════════════════════

use verus_rational::RuntimeRational;

/// Convert a RuntimeRational to f32 by reading the underlying BigInt limbs.
/// Only used for GPU rendering — not verified, just a convenience helper.
fn rational_to_f32(r: &RuntimeRational) -> f32 {
    // Numerator: signed, magnitude stored as little-endian u32 limbs
    let num_neg = r.numerator.is_negative;
    let num_mag = &r.numerator.magnitude.limbs_le;
    let num_val: f64 = limbs_to_f64(num_mag);
    let num = if num_neg { -num_val } else { num_val };

    // Denominator: unsigned, little-endian u32 limbs
    let den_val: f64 = limbs_to_f64(&r.denominator.limbs_le);
    if den_val == 0.0 {
        return 0.0;
    }
    (num / den_val) as f32
}

fn limbs_to_f64(limbs: &[u32]) -> f64 {
    let mut val: f64 = 0.0;
    let mut base: f64 = 1.0;
    for &limb in limbs {
        val += limb as f64 * base;
        base *= 4294967296.0; // 2^32
    }
    val
}

// ═══════════════════════════════════════════════════════════════════════════
// Widget construction helpers
// ═══════════════════════════════════════════════════════════════════════════

use builtin::Ghost;
use verus_gui::runtime::widget::*;
use verus_gui::runtime::size::RuntimeSize;
use verus_gui::runtime::limits::RuntimeLimits;
use verus_gui::runtime::padding::RuntimePadding;
use verus_gui::runtime::node::RuntimeNode;
use verus_gui::runtime::draw::{RuntimeDrawCommand, flatten_node_exec};
use verus_gui::alignment::Alignment;
use verus_gui::widget::FlexDirection;

fn ri(v: i64) -> RuntimeRational {
    RuntimeRational::from_int(v)
}

fn make_size(w: i64, h: i64) -> RuntimeSize {
    RuntimeSize::new(ri(w), ri(h))
}

fn make_padding(all: i64) -> RuntimePadding {
    RuntimePadding::new(ri(all), ri(all), ri(all), ri(all))
}

fn make_padding_zero() -> RuntimePadding {
    RuntimePadding::new(ri(0), ri(0), ri(0), ri(0))
}

fn make_limits(min_w: i64, min_h: i64, max_w: i64, max_h: i64) -> RuntimeLimits {
    RuntimeLimits::new(make_size(min_w, min_h), make_size(max_w, max_h))
}

fn leaf(w: i64, h: i64) -> RuntimeWidget {
    RuntimeWidget::Leaf(RuntimeLeafWidget::Leaf {
        size: make_size(w, h),
        model: Ghost::assume_new(),
    })
}

fn column(padding: i64, spacing: i64, children: Vec<RuntimeWidget>) -> RuntimeWidget {
    RuntimeWidget::Container(RuntimeContainerWidget::Column {
        padding: make_padding(padding),
        spacing: ri(spacing),
        alignment: Alignment::Start,
        children,
        model: Ghost::assume_new(),
    })
}

fn column_aligned(padding: i64, spacing: i64, align: Alignment, children: Vec<RuntimeWidget>) -> RuntimeWidget {
    RuntimeWidget::Container(RuntimeContainerWidget::Column {
        padding: make_padding(padding),
        spacing: ri(spacing),
        alignment: align,
        children,
        model: Ghost::assume_new(),
    })
}

fn row(spacing: i64, children: Vec<RuntimeWidget>) -> RuntimeWidget {
    RuntimeWidget::Container(RuntimeContainerWidget::Row {
        padding: make_padding_zero(),
        spacing: ri(spacing),
        alignment: Alignment::Start,
        children,
        model: Ghost::assume_new(),
    })
}

fn row_aligned(spacing: i64, align: Alignment, children: Vec<RuntimeWidget>) -> RuntimeWidget {
    RuntimeWidget::Container(RuntimeContainerWidget::Row {
        padding: make_padding_zero(),
        spacing: ri(spacing),
        alignment: align,
        children,
        model: Ghost::assume_new(),
    })
}

fn stack(h_align: Alignment, v_align: Alignment, children: Vec<RuntimeWidget>) -> RuntimeWidget {
    RuntimeWidget::Container(RuntimeContainerWidget::Stack {
        padding: make_padding_zero(),
        h_align,
        v_align,
        children,
        model: Ghost::assume_new(),
    })
}

fn wrap(h_spacing: i64, v_spacing: i64, children: Vec<RuntimeWidget>) -> RuntimeWidget {
    RuntimeWidget::Container(RuntimeContainerWidget::Wrap {
        padding: make_padding_zero(),
        h_spacing: ri(h_spacing),
        v_spacing: ri(v_spacing),
        children,
        model: Ghost::assume_new(),
    })
}

fn flex_row(spacing: i64, items: Vec<(i64, RuntimeWidget)>) -> RuntimeWidget {
    let children: Vec<RuntimeFlexItem> = items
        .into_iter()
        .map(|(weight, child)| RuntimeFlexItem {
            weight: ri(weight),
            child,
        })
        .collect();
    RuntimeWidget::Container(RuntimeContainerWidget::Flex {
        padding: make_padding_zero(),
        spacing: ri(spacing),
        alignment: Alignment::Start,
        direction: FlexDirection::Row,
        children,
        model: Ghost::assume_new(),
    })
}

fn grid(
    cols: usize,
    rows: usize,
    col_w: i64,
    row_h: i64,
    h_spacing: i64,
    v_spacing: i64,
    children: Vec<RuntimeWidget>,
) -> RuntimeWidget {
    let col_widths: Vec<RuntimeSize> = (0..cols).map(|_| make_size(col_w, 0)).collect();
    let row_heights: Vec<RuntimeSize> = (0..rows).map(|_| make_size(0, row_h)).collect();
    RuntimeWidget::Container(RuntimeContainerWidget::Grid {
        padding: make_padding_zero(),
        h_spacing: ri(h_spacing),
        v_spacing: ri(v_spacing),
        h_align: Alignment::Start,
        v_align: Alignment::Start,
        col_widths,
        row_heights,
        children,
        model: Ghost::assume_new(),
    })
}

fn absolute(children: Vec<(i64, i64, RuntimeWidget)>) -> RuntimeWidget {
    let abs_children: Vec<RuntimeAbsoluteChild> = children
        .into_iter()
        .map(|(x, y, child)| RuntimeAbsoluteChild {
            x: ri(x),
            y: ri(y),
            child,
        })
        .collect();
    RuntimeWidget::Container(RuntimeContainerWidget::Absolute {
        padding: make_padding_zero(),
        children: abs_children,
        model: Ghost::assume_new(),
    })
}

fn margin(m: i64, child: RuntimeWidget) -> RuntimeWidget {
    RuntimeWidget::Wrapper(RuntimeWrapperWidget::Margin {
        margin: make_padding(m),
        child: Box::new(child),
        model: Ghost::assume_new(),
    })
}

fn sized_box(min_w: i64, min_h: i64, max_w: i64, max_h: i64, child: RuntimeWidget) -> RuntimeWidget {
    RuntimeWidget::Wrapper(RuntimeWrapperWidget::SizedBox {
        inner_limits: make_limits(min_w, min_h, max_w, max_h),
        child: Box::new(child),
        model: Ghost::assume_new(),
    })
}

fn conditional(visible: bool, child: RuntimeWidget) -> RuntimeWidget {
    RuntimeWidget::Wrapper(RuntimeWrapperWidget::Conditional {
        visible,
        child: Box::new(child),
        model: Ghost::assume_new(),
    })
}

fn scroll_view(vw: i64, vh: i64, sx: i64, sy: i64, child: RuntimeWidget) -> RuntimeWidget {
    RuntimeWidget::Wrapper(RuntimeWrapperWidget::ScrollView {
        viewport: make_size(vw, vh),
        scroll_x: ri(sx),
        scroll_y: ri(sy),
        child: Box::new(child),
        model: Ghost::assume_new(),
    })
}

fn listview(spacing: i64, vh: i64, vw: i64, scroll_y: i64, children: Vec<RuntimeWidget>) -> RuntimeWidget {
    RuntimeWidget::Container(RuntimeContainerWidget::ListView {
        spacing: ri(spacing),
        scroll_y: ri(scroll_y),
        viewport: make_size(vw, vh),
        children,
        model: Ghost::assume_new(),
    })
}

// ═══════════════════════════════════════════════════════════════════════════
// Build the showcase widget tree
// ═══════════════════════════════════════════════════════════════════════════

fn build_showcase() -> RuntimeWidget {
    column(10, 12, vec![
        // Section 1: Row — three items side by side
        row(8, vec![
            leaf(80, 40),
            leaf(80, 40),
            leaf(80, 40),
        ]),

        // Section 2: Row with center alignment
        row_aligned(8, Alignment::Center, vec![
            leaf(60, 50),
            leaf(60, 30),
            leaf(60, 50),
        ]),

        // Section 3: Stack — overlapping elements
        stack(Alignment::Center, Alignment::Center, vec![
            leaf(160, 60),
            leaf(80, 30),
        ]),

        // Section 4: Wrap — flowing items
        wrap(6, 6, vec![
            leaf(50, 28),
            leaf(65, 28),
            leaf(45, 28),
            leaf(70, 28),
            leaf(55, 28),
            leaf(60, 28),
        ]),

        // Section 5: Flex — weighted distribution
        flex_row(4, vec![
            (1, leaf(0, 35)),
            (2, leaf(0, 35)),
            (1, leaf(0, 35)),
        ]),

        // Section 6: Grid — 3x2
        grid(3, 2, 80, 35, 6, 6, vec![
            leaf(0, 0), leaf(0, 0), leaf(0, 0),
            leaf(0, 0), leaf(0, 0), leaf(0, 0),
        ]),

        // Section 7: Absolute positioning
        absolute(vec![
            (0,  0,  leaf(200, 70)),
            (15, 10, leaf(60, 25)),
            (90, 30, leaf(60, 25)),
        ]),

        // Section 8: Margin wrapper
        margin(12, leaf(120, 35)),

        // Section 9: SizedBox — clamps a large child
        sized_box(0, 0, 100, 30, leaf(300, 300)),

        // Section 10: Conditional — visible
        conditional(true, leaf(120, 30)),

        // Section 11: Conditional — hidden (should produce zero-size node)
        conditional(false, leaf(120, 30)),

        // Section 12: ScrollView
        scroll_view(200, 50, 0, 10, column(0, 4, vec![
            leaf(180, 25),
            leaf(180, 25),
            leaf(180, 25),
            leaf(180, 25),
        ])),

        // Section 13: ListView
        listview(4, 60, 200, 0, vec![
            leaf(180, 25),
            leaf(180, 25),
            leaf(180, 25),
            leaf(180, 25),
        ]),
    ])
}

// ═══════════════════════════════════════════════════════════════════════════
// Color palette — depth-based coloring
// ═══════════════════════════════════════════════════════════════════════════

const PALETTE: &[(f32, f32, f32)] = &[
    (0.15, 0.15, 0.20),  // depth 0: dark background
    (0.25, 0.35, 0.55),  // depth 1: slate blue sections
    (0.90, 0.45, 0.30),  // depth 2: coral widgets
    (0.30, 0.75, 0.50),  // depth 3: green inner
    (0.85, 0.70, 0.25),  // depth 4: gold
    (0.55, 0.40, 0.80),  // depth 5: purple
    (0.25, 0.70, 0.80),  // depth 6: teal
    (0.90, 0.55, 0.70),  // depth 7: pink
];

fn depth_color(depth: usize) -> (f32, f32, f32) {
    PALETTE[depth % PALETTE.len()]
}

// ═══════════════════════════════════════════════════════════════════════════
// Vulkan backend
// ═══════════════════════════════════════════════════════════════════════════

mod vulkan {
    use super::*;
    use std::sync::Arc;
    use ash::vk;
    use ash::vk::Handle;
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
        pub width: u32,
        pub height: u32,
        // GUI state
        pub draws: Vec<RuntimeDrawCommand>,
    }

    impl VkState {
        pub fn new(window: Arc<Window>) -> Self {
            let size = window.inner_size();
            let width = size.width.max(1);
            let height = size.height.max(1);

            let display_handle = window.display_handle().unwrap();
            let surface_extensions =
                ash_window::enumerate_required_extensions(display_handle.as_raw())
                    .expect("Failed to get required surface extensions");

            let device_exts: Vec<*const i8> = vec![ash::khr::swapchain::NAME.as_ptr()];

            let ctx = unsafe {
                VulkanContext::new("gui_showcase", true, surface_extensions, &device_exts, 0)
            };

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

            let dev = ffi::vk_create_device(&ctx, Ghost::assume_new());
            let queue = ffi::vk_get_device_queue(&ctx, 0, 0, Ghost::assume_new());

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

            // Render pass (single color attachment, no depth)
            let render_pass = ffi::vk_create_render_pass(
                &ctx,
                Ghost::assume_new(),
                format.as_raw() as u32,
                vk::AttachmentLoadOp::CLEAR.as_raw() as u32,
                vk::AttachmentStoreOp::STORE.as_raw() as u32,
                vk::SampleCountFlags::TYPE_1.as_raw() as u32,
            );

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

            // Shader modules
            let vert_code = spv_to_u32(include_bytes!("shaders/gui.vert.spv"));
            let vert_module = ffi::vk_create_shader_module(&ctx, Ghost::assume_new(), &vert_code);

            let frag_code = spv_to_u32(include_bytes!("shaders/gui.frag.spv"));
            let frag_module = ffi::vk_create_shader_module(&ctx, Ghost::assume_new(), &frag_code);

            // Pipeline layout: 32-byte push constant at VERTEX|FRAGMENT stages
            let push_stages = vk::ShaderStageFlags::VERTEX.as_raw()
                | vk::ShaderStageFlags::FRAGMENT.as_raw();
            let pipeline_layout_handle = ffi::vk_create_pipeline_layout_push(
                &ctx,
                &[],
                push_stages,
                0,
                32, // x,y,w,h,r,g,b,a = 8 × f32 = 32 bytes
            );

            // Graphics pipeline (no depth test, no culling)
            let pipeline = ffi::vk_create_graphics_pipeline(
                &ctx,
                Ghost::assume_new(),
                pipeline_layout_handle,
                render_pass.handle,
                vert_module.handle,
                frag_module.handle,
                vk::CullModeFlags::NONE.as_raw(),
                vk::FrontFace::COUNTER_CLOCKWISE.as_raw() as u32,
                false, false, 0,
            );

            // Command pool + buffers
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

            // Sync objects
            let in_flight_fence = ffi::vk_create_fence(&ctx, Ghost::assume_new(), true);
            let image_available_sem = ffi::vk_create_semaphore(&ctx, Ghost::assume_new());
            let render_finished_sem = ffi::vk_create_semaphore(&ctx, Ghost::assume_new());

            // Build widget tree, layout, and flatten to draw commands
            let widget = build_showcase();
            let fuel: usize = 20;
            let limits = make_limits(0, 0, width as i64, height as i64);
            let node = layout_widget_exec(&limits, &widget, fuel);
            let zero_x = ri(0);
            let zero_y = ri(0);
            let draws = flatten_node_exec(&node, &zero_x, &zero_y, 0, fuel);

            eprintln!(
                "GUI showcase initialized: {}x{}, {} draw commands",
                width, height, draws.len()
            );

            VkState {
                ctx, dev, raw_surface, surface, queue, swapchain, image_views,
                render_pass, framebuffers, pipeline, pipeline_layout_handle,
                command_pool, command_buffers, image_available_sem,
                render_finished_sem, in_flight_fence, vert_module, frag_module,
                format, width, height, draws,
            }
        }

        pub fn resize(&mut self, width: u32, height: u32) {
            if width == 0 || height == 0 {
                return;
            }
            self.width = width;
            self.height = height;
            // Re-layout for new viewport
            let widget = build_showcase();
            let fuel: usize = 20;
            let limits = make_limits(0, 0, width as i64, height as i64);
            let node = layout_widget_exec(&limits, &widget, fuel);
            let zero_x = ri(0);
            let zero_y = ri(0);
            self.draws = flatten_node_exec(&node, &zero_x, &zero_y, 0, fuel);
        }

        pub fn render(&mut self) {
            ffi::vk_wait_for_fences(
                &self.ctx, &mut self.in_flight_fence, Ghost::assume_new(), u64::MAX,
            );
            ffi::vk_reset_fences(&self.ctx, &mut self.in_flight_fence);

            let idx = ffi::vk_acquire_next_image(
                &self.ctx,
                &mut self.swapchain,
                self.image_available_sem.handle,
                0,
                u64::MAX,
            );

            let cb = &mut self.command_buffers[idx as usize];

            ffi::vk_begin_command_buffer(&self.ctx, cb);
            ffi::vk_cmd_begin_render_pass(
                &self.ctx,
                Ghost::assume_new(),
                Ghost::assume_new(),
                cb,
                self.render_pass.handle,
                self.framebuffers[idx as usize].handle,
                self.width,
                self.height,
                0.12, 0.12, 0.14, 1.0, // dark background
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

            // Draw each GUI rectangle
            let vw = self.width as f32;
            let vh = self.height as f32;
            let push_stages = vk::ShaderStageFlags::VERTEX.as_raw()
                | vk::ShaderStageFlags::FRAGMENT.as_raw();

            for draw in &self.draws {
                let px = rational_to_f32(&draw.x);
                let py = rational_to_f32(&draw.y);
                let pw = rational_to_f32(&draw.width);
                let ph = rational_to_f32(&draw.height);

                // Skip zero-area draws
                if pw <= 0.0 || ph <= 0.0 {
                    continue;
                }

                // Convert pixel coords to NDC (-1..1)
                let ndc_x = px / vw * 2.0 - 1.0;
                let ndc_y = py / vh * 2.0 - 1.0;
                let ndc_w = pw / vw * 2.0;
                let ndc_h = ph / vh * 2.0;

                let (cr, cg, cb_color) = depth_color(draw.depth);

                let push_data: [f32; 8] = [
                    ndc_x, ndc_y, ndc_w, ndc_h,
                    cr, cg, cb_color, 1.0,
                ];
                let push_bytes: &[u8] = unsafe {
                    std::slice::from_raw_parts(
                        push_data.as_ptr() as *const u8,
                        32,
                    )
                };

                ffi::ffi_cmd_push_constants(
                    &self.ctx,
                    cb.handle,
                    self.pipeline_layout_handle,
                    push_stages,
                    0,
                    push_bytes,
                );
                ffi::vk_cmd_draw(&self.ctx, cb, 6, 1, 0, 0);
            }

            ffi::vk_cmd_end_render_pass(&self.ctx, cb);
            ffi::vk_end_command_buffer(&self.ctx, cb);

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
                self.ctx.device.destroy_pipeline(
                    vk::Pipeline::from_raw(self.pipeline.handle), None);
                self.ctx.device.destroy_pipeline_layout(
                    vk::PipelineLayout::from_raw(self.pipeline_layout_handle), None);
                self.ctx.device.destroy_shader_module(
                    vk::ShaderModule::from_raw(self.vert_module.handle), None);
                self.ctx.device.destroy_shader_module(
                    vk::ShaderModule::from_raw(self.frag_module.handle), None);
                for fb in &self.framebuffers {
                    self.ctx.device.destroy_framebuffer(
                        vk::Framebuffer::from_raw(fb.handle), None);
                }
                for iv in &self.image_views {
                    self.ctx.device.destroy_image_view(
                        vk::ImageView::from_raw(iv.handle), None);
                }
                self.ctx.device.destroy_render_pass(
                    vk::RenderPass::from_raw(self.render_pass.handle), None);
                self.ctx.device.destroy_command_pool(
                    vk::CommandPool::from_raw(self.command_pool.handle), None);
                self.ctx.device.destroy_fence(
                    vk::Fence::from_raw(self.in_flight_fence.handle), None);
                self.ctx.device.destroy_semaphore(
                    vk::Semaphore::from_raw(self.image_available_sem.handle), None);
                self.ctx.device.destroy_semaphore(
                    vk::Semaphore::from_raw(self.render_finished_sem.handle), None);
                self.ctx.swapchain_loader.destroy_swapchain(
                    vk::SwapchainKHR::from_raw(self.swapchain.handle), None);
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

struct App {
    window: Option<std::sync::Arc<Window>>,
    state: Option<vulkan::VkState>,
}

impl ApplicationHandler for App {
    fn resumed(&mut self, event_loop: &ActiveEventLoop) {
        if self.window.is_some() {
            return;
        }
        let attrs = WindowAttributes::default()
            .with_title("Verified GUI Widget Showcase")
            .with_inner_size(winit::dpi::LogicalSize::new(500, 800));
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
