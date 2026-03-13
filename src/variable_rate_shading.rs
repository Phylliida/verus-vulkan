use vstd::prelude::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// Fragment shading rates.
pub enum ShadingRate {
    Rate1x1,
    Rate1x2,
    Rate2x1,
    Rate2x2,
    Rate2x4,
    Rate4x2,
    Rate4x4,
}

/// Combiner operations for combining shading rates from different sources.
pub enum ShadingRateCombinerOp {
    Keep,
    Replace,
    Min,
    Max,
    Mul,
}

/// Tracks the current fragment shading rate state.
pub struct ShadingRateState {
    /// Pipeline-specified shading rate.
    pub pipeline_rate: ShadingRate,
    /// Primitive-specified shading rate.
    pub primitive_rate: ShadingRate,
    /// Attachment-specified shading rate.
    pub attachment_rate: ShadingRate,
    /// Combiner for pipeline vs primitive.
    pub combiner_op_0: ShadingRateCombinerOp,
    /// Combiner for (pipeline+primitive) vs attachment.
    pub combiner_op_1: ShadingRateCombinerOp,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// Default shading rate state: 1x1 everywhere, Keep combiners.
pub open spec fn default_shading_rate_state() -> ShadingRateState {
    ShadingRateState {
        pipeline_rate: ShadingRate::Rate1x1,
        primitive_rate: ShadingRate::Rate1x1,
        attachment_rate: ShadingRate::Rate1x1,
        combiner_op_0: ShadingRateCombinerOp::Keep,
        combiner_op_1: ShadingRateCombinerOp::Keep,
    }
}

/// Ghost update: set the fragment shading rate (pipeline rate + combiner ops).
pub open spec fn set_fragment_shading_rate(
    state: ShadingRateState,
    rate: ShadingRate,
    combiner0: ShadingRateCombinerOp,
    combiner1: ShadingRateCombinerOp,
) -> ShadingRateState {
    ShadingRateState {
        pipeline_rate: rate,
        combiner_op_0: combiner0,
        combiner_op_1: combiner1,
        ..state
    }
}

/// A shading rate state is well-formed.
pub open spec fn shading_rate_well_formed(state: ShadingRateState) -> bool {
    true // All enum values are valid by construction.
}

/// Get the texel size (width * height) for a shading rate.
pub open spec fn shading_rate_texel_size(rate: ShadingRate) -> nat {
    match rate {
        ShadingRate::Rate1x1 => 1,
        ShadingRate::Rate1x2 => 2,
        ShadingRate::Rate2x1 => 2,
        ShadingRate::Rate2x2 => 4,
        ShadingRate::Rate2x4 => 8,
        ShadingRate::Rate4x2 => 8,
        ShadingRate::Rate4x4 => 16,
    }
}

/// Get the width component of a shading rate.
pub open spec fn shading_rate_width(rate: ShadingRate) -> nat {
    match rate {
        ShadingRate::Rate1x1 => 1,
        ShadingRate::Rate1x2 => 1,
        ShadingRate::Rate2x1 => 2,
        ShadingRate::Rate2x2 => 2,
        ShadingRate::Rate2x4 => 2,
        ShadingRate::Rate4x2 => 4,
        ShadingRate::Rate4x4 => 4,
    }
}

/// Get the height component of a shading rate.
pub open spec fn shading_rate_height(rate: ShadingRate) -> nat {
    match rate {
        ShadingRate::Rate1x1 => 1,
        ShadingRate::Rate1x2 => 2,
        ShadingRate::Rate2x1 => 1,
        ShadingRate::Rate2x2 => 2,
        ShadingRate::Rate2x4 => 4,
        ShadingRate::Rate4x2 => 2,
        ShadingRate::Rate4x4 => 4,
    }
}

/// An attachment shading rate image is valid with respect to framebuffer dimensions.
pub open spec fn attachment_shading_rate_valid(
    image_width: nat,
    image_height: nat,
    fb_width: nat,
    fb_height: nat,
    texel_width: nat,
    texel_height: nat,
) -> bool {
    texel_width > 0
    && texel_height > 0
    && image_width * texel_width >= fb_width
    && image_height * texel_height >= fb_height
}

// ── Lemmas ──────────────────────────────────────────────────────────────

/// Default shading rate state is well-formed.
pub proof fn lemma_default_well_formed()
    ensures shading_rate_well_formed(default_shading_rate_state()),
{
}

/// 1x1 shading rate has texel size 1 (identity).
pub proof fn lemma_1x1_is_identity()
    ensures shading_rate_texel_size(ShadingRate::Rate1x1) == 1,
{
}

/// Texel size is always positive.
pub proof fn lemma_texel_size_positive(rate: ShadingRate)
    ensures shading_rate_texel_size(rate) > 0,
{
}

/// Texel size equals width * height.
pub proof fn lemma_texel_size_is_product(rate: ShadingRate)
    ensures
        shading_rate_texel_size(rate)
            == shading_rate_width(rate) * shading_rate_height(rate),
{
}

/// Setting fragment shading rate preserves attachment and primitive rates.
pub proof fn lemma_set_rate_preserves_attachment(
    state: ShadingRateState,
    rate: ShadingRate,
    c0: ShadingRateCombinerOp,
    c1: ShadingRateCombinerOp,
)
    ensures
        set_fragment_shading_rate(state, rate, c0, c1).attachment_rate == state.attachment_rate,
        set_fragment_shading_rate(state, rate, c0, c1).primitive_rate == state.primitive_rate,
{
}

} // verus!
