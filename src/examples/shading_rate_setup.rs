//! # Example: Fragment Shading Rate Setup
//!
//! Models configuring variable-rate shading for a rendering pipeline:
//!   1. Define device properties (what the GPU supports)
//!   2. Create an FSR attachment image covering a 1920x1080 framebuffer
//!   3. Configure two-stage combination: pipeline rate + attachment rate
//!   4. Prove the effective rate is valid for the device
//!   5. Show depth clamping interop (ZeroOne mode with depth test)
//!
//! Demonstrates how FSR, VRS, and depth clamp modules compose.

use vstd::prelude::*;
use crate::variable_rate_shading;
use crate::variable_rate_shading::*;
use crate::fragment_shading_rate::*;
use crate::depth_clamp_control;
use crate::depth_clamp_control::*;
use crate::depth_stencil::*;

verus! {

// ── Device Configuration ────────────────────────────────────────────────

/// Typical device FSR properties (like a modern NVIDIA/AMD GPU).
pub open spec fn gpu_fsr_properties() -> FragmentShadingRateProperties {
    FragmentShadingRateProperties {
        min_texel_size_width: 1,
        min_texel_size_height: 1,
        max_texel_size_width: 4,
        max_texel_size_height: 4,
        max_fragment_size_width: 4,
        max_fragment_size_height: 4,
        supports_non_square: true,  // most modern GPUs support this
    }
}

/// A more conservative device that only supports square rates.
pub open spec fn square_only_properties() -> FragmentShadingRateProperties {
    FragmentShadingRateProperties {
        min_texel_size_width: 1,
        min_texel_size_height: 1,
        max_texel_size_width: 4,
        max_texel_size_height: 4,
        max_fragment_size_width: 4,
        max_fragment_size_height: 4,
        supports_non_square: false,
    }
}

// ── Step-by-step Proofs ─────────────────────────────────────────────────

/// Step 1: Device properties are valid.
pub proof fn step1_properties_valid()
    ensures
        fsr_properties_valid(gpu_fsr_properties()),
        fsr_properties_valid(square_only_properties()),
{
}

/// Step 2: Create an FSR attachment that covers a 1920x1080 framebuffer.
/// The image uses 4x4 texel size (max supported), so we need 480x270 texels.
/// 480 * 4 = 1920 >= 1920, 270 * 4 = 1080 >= 1080.
pub proof fn step2_create_attachment()
    ensures ({
        let att = create_fsr_attachment(42, 4, 4, 1);  // view=42, 4x4 texels, 1 layer
        fsr_attachment_well_formed(att, gpu_fsr_properties())
        && att.layer_count == 1
        && att.texel_width == 4
        && att.texel_height == 4
    }),
{
    lemma_create_attachment_layer_count(42, 4, 4, 1);
}

/// Step 3: Prove the attachment covers the framebuffer.
/// 480 * 4 = 1920 >= 1920, 270 * 4 = 1080 >= 1080.
pub proof fn step3_attachment_covers_framebuffer()
    ensures ({
        let att = create_fsr_attachment(42, 4, 4, 1);
        fsr_attachment_covers_framebuffer(att, 480, 270, 1920, 1080)
    }),
{
    assert(480 * 4 >= 1920) by(nonlinear_arith);
    assert(270 * 4 >= 1080) by(nonlinear_arith);
}

/// Step 4: Configure shading rate with Keep/Keep combiners.
/// Pipeline rate of 2x2 propagates through unchanged.
pub proof fn step4_keep_keep_propagates()
    ensures ({
        let state = ShadingRateState {
            pipeline_rate: ShadingRate::Rate2x2,
            primitive_rate: ShadingRate::Rate1x1,
            attachment_rate: ShadingRate::Rate4x4,
            combiner_op_0: ShadingRateCombinerOp::Keep,
            combiner_op_1: ShadingRateCombinerOp::Keep,
        };
        fsr_effective_rate(state) == ShadingRate::Rate2x2
    }),
{
    let state = ShadingRateState {
        pipeline_rate: ShadingRate::Rate2x2,
        primitive_rate: ShadingRate::Rate1x1,
        attachment_rate: ShadingRate::Rate4x4,
        combiner_op_0: ShadingRateCombinerOp::Keep,
        combiner_op_1: ShadingRateCombinerOp::Keep,
    };
    lemma_fsr_effective_rate_with_keep_keep(state);
}

/// Step 5: Replace/Keep — primitive overrides pipeline, attachment ignored.
pub proof fn step5_replace_keep()
    ensures ({
        let state = ShadingRateState {
            pipeline_rate: ShadingRate::Rate1x1,
            primitive_rate: ShadingRate::Rate4x4,
            attachment_rate: ShadingRate::Rate2x2,
            combiner_op_0: ShadingRateCombinerOp::Replace,  // stage1 = primitive = 4x4
            combiner_op_1: ShadingRateCombinerOp::Keep,     // stage2 = keep stage1 = 4x4
        };
        fsr_effective_rate(state) == ShadingRate::Rate4x4
    }),
{
}

/// Step 6: On a square-only device, using Keep/Keep with square rates is safe.
pub proof fn step6_square_device_safe()
    ensures ({
        let state = ShadingRateState {
            pipeline_rate: ShadingRate::Rate2x2,
            primitive_rate: ShadingRate::Rate1x1,
            attachment_rate: ShadingRate::Rate1x1,
            combiner_op_0: ShadingRateCombinerOp::Keep,
            combiner_op_1: ShadingRateCombinerOp::Keep,
        };
        fsr_effective_rate_device_valid(state, square_only_properties())
    }),
{
    let state = ShadingRateState {
        pipeline_rate: ShadingRate::Rate2x2,
        primitive_rate: ShadingRate::Rate1x1,
        attachment_rate: ShadingRate::Rate1x1,
        combiner_op_0: ShadingRateCombinerOp::Keep,
        combiner_op_1: ShadingRateCombinerOp::Keep,
    };
    lemma_fsr_keep_keep_square_valid(state, square_only_properties());
}

/// Step 7: All rates have positive fragment area (no zero-pixel fragments).
pub proof fn step7_all_rates_positive_area()
    ensures
        fsr_fragment_area(ShadingRate::Rate1x1) > 0,
        fsr_fragment_area(ShadingRate::Rate2x2) > 0,
        fsr_fragment_area(ShadingRate::Rate4x4) > 0,
{
    lemma_fsr_fragment_area_positive(ShadingRate::Rate1x1);
    lemma_fsr_fragment_area_positive(ShadingRate::Rate2x2);
    lemma_fsr_fragment_area_positive(ShadingRate::Rate4x4);
}

/// Step 8: Default VRS state produces 1x1 effective rate.
pub proof fn step8_default_is_1x1()
    ensures fsr_effective_rate(default_shading_rate_state()) == ShadingRate::Rate1x1,
{
    lemma_fsr_effective_rate_with_keep_keep(default_shading_rate_state());
}

// ── Depth Clamp Interop ─────────────────────────────────────────────────

/// Using ZeroOne depth clamp with depth-less testing.
/// Proves clamped values stay in [0,1], compatible with standard depth buffer.
pub proof fn depth_clamp_with_depth_test()
    ensures ({
        let clamp = set_depth_clamp_mode(
            default_depth_clamp_state(),
            DepthClampMode::ZeroOne,
            DepthClampRange { min_depth: 0, max_depth: 1 },
        );
        depth_clamp_state_well_formed(clamp)
        && depth_clamp_affects_output(clamp)
        && depth_stencil_well_formed(depth_test_less())
    }),
{
    let clamp = set_depth_clamp_mode(
        default_depth_clamp_state(),
        DepthClampMode::ZeroOne,
        DepthClampRange { min_depth: 0, max_depth: 1 },
    );
    lemma_set_mode_preserves_structure(
        default_depth_clamp_state(),
        DepthClampMode::ZeroOne,
        DepthClampRange { min_depth: 0, max_depth: 1 },
    );
    lemma_depth_test_less_well_formed();
}

/// Disabled clamp doesn't interfere with depth testing.
pub proof fn disabled_clamp_safe()
    ensures ({
        let clamp = default_depth_clamp_state();
        depth_clamp_state_well_formed(clamp)
        && !depth_clamp_affects_output(clamp)
    }),
{
    depth_clamp_control::lemma_default_well_formed();
    depth_clamp_control::lemma_default_no_clamp();
}

} // verus!
