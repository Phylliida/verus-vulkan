//! # Example: Rendering a Triangle
//!
//! Models the classic "hello triangle" Vulkan workflow:
//!   1. Create a render pass with one color attachment (subpass 0)
//!   2. Create a graphics pipeline for that render pass
//!   3. Begin recording a command buffer
//!   4. Begin the render pass
//!   5. Bind the pipeline
//!   6. Set dynamic viewport + scissor
//!   7. Draw 3 vertices (the triangle)
//!   8. End the render pass
//!
//! Each step is a ghost state transition. The final proof ties them together
//! to show that draw_call_valid holds at the draw site.

use vstd::prelude::*;
use crate::render_pass::*;
use crate::pipeline::*;
use crate::recording::*;
use crate::depth_stencil::*;
use crate::image_layout::*;
use crate::subpass_dep::*;

verus! {

//  ── Scene Setup ─────────────────────────────────────────────────────────

///  A minimal render pass: one color attachment, one subpass, no depth.
pub open spec fn triangle_render_pass() -> RenderPassState {
    RenderPassState {
        id: 1,
        attachments: seq![
            AttachmentDescription {
                format: 44,  //  B8G8R8A8_SRGB
                samples: 1,
                load_op: LoadOp::Clear,
                store_op: StoreOp::Store,
                initial_layout: ImageLayout::Undefined,
                final_layout: ImageLayout::PresentSrc,
            },
        ],
        subpasses: seq![
            SubpassDescription {
                color_attachments: seq![
                    AttachmentReference {
                        attachment_index: 0,
                        layout: ImageLayout::ColorAttachmentOptimal,
                    },
                ],
                depth_attachment: None,
                input_attachments: Seq::empty(),
                preserve_attachments: Set::empty(),
            },
        ],
        dependencies: Seq::empty(),
        extended_dependencies: Seq::empty(),
        alive: true,
    }
}

///  A graphics pipeline created for our triangle render pass, subpass 0.
///  Uses dynamic viewport and scissor (most common setup).
pub open spec fn triangle_pipeline() -> GraphicsPipelineState {
    GraphicsPipelineState {
        id: 100,
        render_pass_id: 1,
        subpass_index: 0,
        descriptor_set_layouts: Seq::empty(),  //  no descriptors for a basic triangle
        color_attachment_count: 1,
        has_depth_attachment: false,
        alive: true,
        required_dynamic_states: set![DynamicStateKind::Viewport, DynamicStateKind::Scissor],
    }
}

//  ── Step-by-step Proofs ─────────────────────────────────────────────────

///  Step 1: The render pass is well-formed.
pub proof fn step1_render_pass_valid()
    ensures
        triangle_render_pass().alive,
        triangle_render_pass().subpasses.len() == 1,
        triangle_render_pass().attachments.len() == 1,
{
}

///  Step 2: The pipeline is compatible with subpass 0 of our render pass.
pub proof fn step2_pipeline_compatible()
    ensures
        graphics_pipeline_compatible_with_subpass(
            triangle_pipeline(),
            triangle_render_pass(),
            0,
        ),
{
    //  Pipeline's render_pass_id matches, subpass_index == 0,
    //  color_attachment_count == 1 (matching subpass 0's 1 color attachment),
    //  has_depth_attachment == false (matching subpass 0's None depth).
}

///  Step 3: Starting from a fresh recording state, begin the render pass.
///  Proves we enter a render pass and the pipeline bindings are preserved.
pub proof fn step3_begin_render_pass()
    ensures ({
        let s0 = initial_recording_state();
        let s1 = begin_render_pass_recording(s0, 1, 42);  //  rp_id=1, fb_id=42
        in_render_pass(s1)
        && s1.active_render_pass.unwrap().render_pass_id == 1
        && s1.active_render_pass.unwrap().framebuffer_id == 42
        && s1.active_render_pass.unwrap().subpass_index == 0
    }),
{
}

///  Step 4: Bind the pipeline inside the render pass.
///  Proves the pipeline is recorded and render pass state is preserved.
pub proof fn step4_bind_pipeline()
    ensures ({
        let s0 = initial_recording_state();
        let s1 = begin_render_pass_recording(s0, 1, 42);
        let s2 = bind_graphics_pipeline(s1, 100, Seq::empty());
        s2.bound_graphics_pipeline == Some(100nat)
        && in_render_pass(s2)  //  render pass still active
        && s2.active_render_pass == s1.active_render_pass  //  unchanged
    }),
{
    let s0 = initial_recording_state();
    let s1 = begin_render_pass_recording(s0, 1, 42);
    lemma_bind_pipeline_preserves_render_pass(s1, 100, Seq::empty());
}

///  Step 5: Set dynamic viewport and scissor, then verify dynamic state satisfied.
pub proof fn step5_set_dynamic_state()
    ensures ({
        let s0 = initial_recording_state();
        let s1 = begin_render_pass_recording(s0, 1, 42);
        let s2 = bind_graphics_pipeline(s1, 100, Seq::empty());
        let s3 = set_viewport_recording(s2);
        let s4 = set_scissor_recording(s3);
        dynamic_state_satisfied(s4, true, true)
        && in_render_pass(s4)
    }),
{
    let s0 = initial_recording_state();
    let s1 = begin_render_pass_recording(s0, 1, 42);
    let s2 = bind_graphics_pipeline(s1, 100, Seq::empty());
    let s3 = set_viewport_recording(s2);
    let s4 = set_scissor_recording(s3);
    lemma_bind_pipeline_preserves_render_pass(s1, 100, Seq::empty());
    lemma_set_viewport_preserves_render_pass(s2);
    lemma_set_scissor_preserves_render_pass(s3);
}

///  Step 6 (final): The draw call is valid!
///  Ties everything together: render pass active + pipeline bound + compatible.
pub proof fn step6_draw_call_valid()
    ensures ({
        let s0 = initial_recording_state();
        let s1 = begin_render_pass_recording(s0, 1, 42);
        let s2 = bind_graphics_pipeline(s1, 100, Seq::empty());
        let s3 = set_viewport_recording(s2);
        let s4 = set_scissor_recording(s3);
        draw_call_valid(s4, triangle_pipeline(), triangle_render_pass())
    }),
{
    let s0 = initial_recording_state();
    let s1 = begin_render_pass_recording(s0, 1, 42);
    let s2 = bind_graphics_pipeline(s1, 100, Seq::empty());
    lemma_bind_pipeline_preserves_render_pass(s1, 100, Seq::empty());
    lemma_set_viewport_preserves_render_pass(s2);
    let s3 = set_viewport_recording(s2);
    lemma_set_scissor_preserves_render_pass(s3);
}

///  After drawing: end the render pass and verify we're back outside.
pub proof fn step7_end_render_pass()
    ensures ({
        let s0 = initial_recording_state();
        let s1 = begin_render_pass_recording(s0, 1, 42);
        let s2 = bind_graphics_pipeline(s1, 100, Seq::empty());
        let s3 = set_viewport_recording(s2);
        let s4 = set_scissor_recording(s3);
        //  ... draw happens here (ghost state unchanged by draw) ...
        let s5 = end_render_pass_recording(s4);
        !in_render_pass(s5)
    }),
{
}

///  The full pipeline: no depth/stencil is compatible with this setup.
pub proof fn triangle_no_depth_stencil()
    ensures
        depth_stencil_well_formed(no_depth_stencil()),
        depth_stencil_compatible_with_attachment(no_depth_stencil(), false),
{
    lemma_no_depth_stencil_well_formed();
    lemma_no_depth_stencil_always_compatible(false);
}

} //  verus!
