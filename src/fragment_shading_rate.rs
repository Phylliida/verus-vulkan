use vstd::prelude::*;
use crate::variable_rate_shading::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// Fragment shading rate attachment descriptor.
pub struct FragmentShadingRateAttachment {
    pub image_view: nat,
    pub texel_width: nat,
    pub texel_height: nat,
    pub layer_count: nat,
}

/// Device properties for fragment shading rate support.
pub struct FragmentShadingRateProperties {
    pub min_texel_size_width: nat,
    pub min_texel_size_height: nat,
    pub max_texel_size_width: nat,
    pub max_texel_size_height: nat,
    pub max_fragment_size_width: nat,
    pub max_fragment_size_height: nat,
    pub supports_non_square: bool,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// A fragment shading rate attachment is well-formed with respect to device properties.
pub open spec fn fsr_attachment_well_formed(
    att: FragmentShadingRateAttachment,
    props: FragmentShadingRateProperties,
) -> bool {
    att.texel_width >= props.min_texel_size_width
    && att.texel_width <= props.max_texel_size_width
    && att.texel_height >= props.min_texel_size_height
    && att.texel_height <= props.max_texel_size_height
    && att.layer_count > 0
    && att.texel_width > 0
    && att.texel_height > 0
}

/// A fragment shading rate attachment covers the entire framebuffer.
/// Requires image dimensions — the image * texel must span the framebuffer.
pub open spec fn fsr_attachment_covers_framebuffer(
    att: FragmentShadingRateAttachment,
    image_width: nat,
    image_height: nat,
    fb_width: nat,
    fb_height: nat,
) -> bool {
    att.texel_width > 0
    && att.texel_height > 0
    && fb_width > 0
    && fb_height > 0
    && image_width * att.texel_width >= fb_width
    && image_height * att.texel_height >= fb_height
}

/// Fragment shading rate properties are valid.
pub open spec fn fsr_properties_valid(props: FragmentShadingRateProperties) -> bool {
    props.min_texel_size_width <= props.max_texel_size_width
    && props.min_texel_size_height <= props.max_texel_size_height
    && props.max_texel_size_width > 0
    && props.max_texel_size_height > 0
    && props.max_fragment_size_width > 0
    && props.max_fragment_size_height > 0
}

/// Clamp a combined width/height to the nearest valid shading rate dimension (1, 2, or 4).
pub open spec fn clamp_shading_dim(d: nat) -> nat {
    if d <= 1 { 1 }
    else if d <= 2 { 2 }
    else { 4 }
}

/// Look up the ShadingRate for a (clamped_width, clamped_height) pair.
pub open spec fn shading_rate_from_dims(w: nat, h: nat) -> ShadingRate {
    if w == 1 && h == 1 { ShadingRate::Rate1x1 }
    else if w == 1 && h == 2 { ShadingRate::Rate1x2 }
    else if w == 2 && h == 1 { ShadingRate::Rate2x1 }
    else if w == 2 && h == 2 { ShadingRate::Rate2x2 }
    else if w == 2 && h == 4 { ShadingRate::Rate2x4 }
    else if w == 4 && h == 2 { ShadingRate::Rate4x2 }
    else { ShadingRate::Rate4x4 } // 4x4 or any overflow
}

/// Combine two shading rates using a combiner operation.
pub open spec fn fsr_combine(
    rate_a: ShadingRate,
    rate_b: ShadingRate,
    op: ShadingRateCombinerOp,
) -> ShadingRate {
    match op {
        ShadingRateCombinerOp::Keep => rate_a,
        ShadingRateCombinerOp::Replace => rate_b,
        ShadingRateCombinerOp::Min => {
            if shading_rate_texel_size(rate_a) <= shading_rate_texel_size(rate_b) {
                rate_a
            } else {
                rate_b
            }
        },
        ShadingRateCombinerOp::Max => {
            if shading_rate_texel_size(rate_a) >= shading_rate_texel_size(rate_b) {
                rate_a
            } else {
                rate_b
            }
        },
        ShadingRateCombinerOp::Mul => {
            let w = clamp_shading_dim(shading_rate_width(rate_a) * shading_rate_width(rate_b));
            let h = clamp_shading_dim(shading_rate_height(rate_a) * shading_rate_height(rate_b));
            shading_rate_from_dims(w, h)
        },
    }
}

/// Compute the effective shading rate through two-stage combination.
pub open spec fn fsr_effective_rate(state: ShadingRateState) -> ShadingRate {
    let stage1 = fsr_combine(state.pipeline_rate, state.primitive_rate, state.combiner_op_0);
    fsr_combine(stage1, state.attachment_rate, state.combiner_op_1)
}

/// Fragment area for a shading rate (alias for texel size).
pub open spec fn fsr_fragment_area(rate: ShadingRate) -> nat {
    shading_rate_texel_size(rate)
}

/// Construct a fragment shading rate attachment.
pub open spec fn create_fsr_attachment(
    view: nat,
    tw: nat,
    th: nat,
    layers: nat,
) -> FragmentShadingRateAttachment {
    FragmentShadingRateAttachment {
        image_view: view,
        texel_width: tw,
        texel_height: th,
        layer_count: layers,
    }
}

/// Whether a shading rate is square (width == height).
pub open spec fn fsr_rate_is_square(rate: ShadingRate) -> bool {
    shading_rate_width(rate) == shading_rate_height(rate)
}

/// A shading rate is valid for a device — must be square unless device supports non-square.
pub open spec fn fsr_rate_device_valid(rate: ShadingRate, props: FragmentShadingRateProperties) -> bool {
    fsr_rate_is_square(rate) || props.supports_non_square
}

/// The effective shading rate is valid for the device.
/// Caller must prove this to ensure the two-stage combiner didn't produce
/// an unsupported non-square rate (e.g. Mul producing 2x4 on a square-only device).
pub open spec fn fsr_effective_rate_device_valid(
    state: ShadingRateState,
    props: FragmentShadingRateProperties,
) -> bool {
    fsr_rate_device_valid(fsr_effective_rate(state), props)
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// Keep combiner returns the first rate.
pub proof fn lemma_fsr_keep_returns_first(a: ShadingRate, b: ShadingRate)
    ensures fsr_combine(a, b, ShadingRateCombinerOp::Keep) == a,
{
}

/// Replace combiner returns the second rate.
pub proof fn lemma_fsr_replace_returns_second(a: ShadingRate, b: ShadingRate)
    ensures fsr_combine(a, b, ShadingRateCombinerOp::Replace) == b,
{
}

/// Keep with 1x1 returns 1x1.
pub proof fn lemma_fsr_1x1_identity_keep(b: ShadingRate)
    ensures fsr_combine(ShadingRate::Rate1x1, b, ShadingRateCombinerOp::Keep)
        == ShadingRate::Rate1x1,
{
}

/// All shading rates have positive fragment area.
pub proof fn lemma_fsr_fragment_area_positive(rate: ShadingRate)
    ensures fsr_fragment_area(rate) > 0,
{
}

/// Well-formed attachment has positive texel dimensions.
pub proof fn lemma_fsr_attachment_covers(
    att: FragmentShadingRateAttachment,
    props: FragmentShadingRateProperties,
)
    requires fsr_attachment_well_formed(att, props),
    ensures att.texel_width > 0 && att.texel_height > 0,
{
}

/// Valid properties have positive max texel sizes.
pub proof fn lemma_fsr_properties_valid_has_max(props: FragmentShadingRateProperties)
    requires fsr_properties_valid(props),
    ensures props.max_texel_size_width > 0 && props.max_texel_size_height > 0,
{
}

/// Both Keep combiners → effective rate == pipeline rate.
pub proof fn lemma_fsr_effective_rate_with_keep_keep(state: ShadingRateState)
    requires
        matches!(state.combiner_op_0, ShadingRateCombinerOp::Keep),
        matches!(state.combiner_op_1, ShadingRateCombinerOp::Keep),
    ensures fsr_effective_rate(state) == state.pipeline_rate,
{
}

/// 1x1, 2x2, and 4x4 are square rates.
pub proof fn lemma_fsr_square_rates_square()
    ensures
        fsr_rate_is_square(ShadingRate::Rate1x1),
        fsr_rate_is_square(ShadingRate::Rate2x2),
        fsr_rate_is_square(ShadingRate::Rate4x4),
{
}

/// Constructor preserves layer count.
pub proof fn lemma_create_attachment_layer_count(
    view: nat,
    tw: nat,
    th: nat,
    layers: nat,
)
    ensures create_fsr_attachment(view, tw, th, layers).layer_count == layers,
{
}

/// Non-square rates: 1x2, 2x1, 2x4, 4x2 are not square.
pub proof fn lemma_fsr_non_square_requires_support()
    ensures
        !fsr_rate_is_square(ShadingRate::Rate1x2),
        !fsr_rate_is_square(ShadingRate::Rate2x1),
        !fsr_rate_is_square(ShadingRate::Rate2x4),
        !fsr_rate_is_square(ShadingRate::Rate4x2),
{
}

/// Mul with 1x1 is identity: 1x1 * X == X for all rates.
pub proof fn lemma_fsr_mul_1x1_identity(rate: ShadingRate)
    ensures fsr_combine(ShadingRate::Rate1x1, rate, ShadingRateCombinerOp::Mul) == rate,
{
    // 1x1 has width=1, height=1, so 1*w=w, 1*h=h, clamp preserves valid dims
}

/// Keep/Keep with a square pipeline rate is always device-valid (no non-square support needed).
pub proof fn lemma_fsr_keep_keep_square_valid(
    state: ShadingRateState,
    props: FragmentShadingRateProperties,
)
    requires
        matches!(state.combiner_op_0, ShadingRateCombinerOp::Keep),
        matches!(state.combiner_op_1, ShadingRateCombinerOp::Keep),
        fsr_rate_is_square(state.pipeline_rate),
    ensures fsr_effective_rate_device_valid(state, props),
{
}

/// All square rates are device-valid regardless of non-square support.
pub proof fn lemma_fsr_square_always_device_valid(
    rate: ShadingRate,
    props: FragmentShadingRateProperties,
)
    requires fsr_rate_is_square(rate),
    ensures fsr_rate_device_valid(rate, props),
{
}

/// Attachment must actually cover the framebuffer — caller must provide image dimensions.
pub proof fn lemma_fsr_coverage_requires_sufficient_image(
    att: FragmentShadingRateAttachment,
    image_width: nat,
    image_height: nat,
    fb_width: nat,
    fb_height: nat,
)
    requires fsr_attachment_covers_framebuffer(att, image_width, image_height, fb_width, fb_height),
    ensures
        image_width * att.texel_width >= fb_width,
        image_height * att.texel_height >= fb_height,
{
}

} // verus!
