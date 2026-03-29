use vstd::prelude::*;

verus! {

//  ── Types ───────────────────────────────────────────────────────────────

///  Color blend factor.
pub enum BlendFactor {
    Zero,
    One,
    SrcColor,
    OneMinusSrcColor,
    DstColor,
    OneMinusDstColor,
    SrcAlpha,
    OneMinusSrcAlpha,
    DstAlpha,
    OneMinusDstAlpha,
    ConstantColor,
    OneMinusConstantColor,
    ConstantAlpha,
    OneMinusConstantAlpha,
    SrcAlphaSaturate,
}

///  Color blend operation.
pub enum BlendOp {
    Add,
    Subtract,
    ReverseSubtract,
    Min,
    Max,
}

///  Color component write mask flags.
pub struct ColorWriteMask {
    pub r: bool,
    pub g: bool,
    pub b: bool,
    pub a: bool,
}

///  Per-attachment color blend state.
pub struct AttachmentBlendState {
    pub blend_enable: bool,
    pub src_color_blend_factor: BlendFactor,
    pub dst_color_blend_factor: BlendFactor,
    pub color_blend_op: BlendOp,
    pub src_alpha_blend_factor: BlendFactor,
    pub dst_alpha_blend_factor: BlendFactor,
    pub alpha_blend_op: BlendOp,
    pub color_write_mask: ColorWriteMask,
}

///  Full color blend state for a graphics pipeline.
pub struct ColorBlendState {
    ///  Per-attachment blend states.
    pub attachments: Seq<AttachmentBlendState>,
    ///  Blend constants (used with ConstantColor/ConstantAlpha factors).
    pub blend_constants_needed: bool,
}

//  ── Spec Functions ──────────────────────────────────────────────────────

///  Color blend state attachment count matches pipeline's color attachment count.
pub open spec fn blend_attachment_count_matches(
    state: ColorBlendState,
    color_attachment_count: nat,
) -> bool {
    state.attachments.len() == color_attachment_count
}

///  An attachment blend state uses constant blend factors.
pub open spec fn uses_constant_factors(state: AttachmentBlendState) -> bool {
    state.blend_enable && (
        blend_factor_is_constant(state.src_color_blend_factor)
        || blend_factor_is_constant(state.dst_color_blend_factor)
        || blend_factor_is_constant(state.src_alpha_blend_factor)
        || blend_factor_is_constant(state.dst_alpha_blend_factor)
    )
}

///  A blend factor references blend constants.
pub open spec fn blend_factor_is_constant(factor: BlendFactor) -> bool {
    factor == BlendFactor::ConstantColor
    || factor == BlendFactor::OneMinusConstantColor
    || factor == BlendFactor::ConstantAlpha
    || factor == BlendFactor::OneMinusConstantAlpha
}

///  If any attachment uses constant factors, blend constants must be set.
pub open spec fn blend_constants_required(state: ColorBlendState) -> bool {
    exists|i: int| 0 <= i < state.attachments.len()
        && uses_constant_factors(#[trigger] state.attachments[i])
}

///  Color blend state is well-formed.
pub open spec fn color_blend_well_formed(state: ColorBlendState) -> bool {
    blend_constants_required(state) ==> state.blend_constants_needed
}

///  Default blend state: no blending, write all components.
pub open spec fn default_attachment_blend() -> AttachmentBlendState {
    AttachmentBlendState {
        blend_enable: false,
        src_color_blend_factor: BlendFactor::One,
        dst_color_blend_factor: BlendFactor::Zero,
        color_blend_op: BlendOp::Add,
        src_alpha_blend_factor: BlendFactor::One,
        dst_alpha_blend_factor: BlendFactor::Zero,
        alpha_blend_op: BlendOp::Add,
        color_write_mask: ColorWriteMask { r: true, g: true, b: true, a: true },
    }
}

///  Standard alpha blending (src_alpha, 1-src_alpha).
pub open spec fn alpha_blend() -> AttachmentBlendState {
    AttachmentBlendState {
        blend_enable: true,
        src_color_blend_factor: BlendFactor::SrcAlpha,
        dst_color_blend_factor: BlendFactor::OneMinusSrcAlpha,
        color_blend_op: BlendOp::Add,
        src_alpha_blend_factor: BlendFactor::One,
        dst_alpha_blend_factor: BlendFactor::Zero,
        alpha_blend_op: BlendOp::Add,
        color_write_mask: ColorWriteMask { r: true, g: true, b: true, a: true },
    }
}

//  ── Proofs ──────────────────────────────────────────────────────────────

///  Default blend doesn't use constant factors.
pub proof fn lemma_default_blend_no_constants()
    ensures !uses_constant_factors(default_attachment_blend()),
{
}

///  Alpha blend doesn't use constant factors.
pub proof fn lemma_alpha_blend_no_constants()
    ensures !uses_constant_factors(alpha_blend()),
{
}

///  A single default attachment matches a pipeline with 1 color attachment.
pub proof fn lemma_single_default_matches()
    ensures
        blend_attachment_count_matches(
            ColorBlendState {
                attachments: seq![default_attachment_blend()],
                blend_constants_needed: false,
            },
            1,
        ),
{
}

///  Empty attachments matches zero color attachments.
pub proof fn lemma_empty_matches_zero()
    ensures
        blend_attachment_count_matches(
            ColorBlendState {
                attachments: Seq::empty(),
                blend_constants_needed: false,
            },
            0,
        ),
{
}

///  If no attachment enables blending, no blend constants are required.
pub proof fn lemma_no_blend_no_constants(state: ColorBlendState)
    requires
        forall|i: int| 0 <= i < state.attachments.len()
            ==> !(#[trigger] state.attachments[i]).blend_enable,
    ensures
        !blend_constants_required(state),
{
    if blend_constants_required(state) {
        let i = choose|i: int| 0 <= i < state.attachments.len()
            && uses_constant_factors(#[trigger] state.attachments[i]);
        assert(state.attachments[i].blend_enable);
    }
}

} //  verus!
