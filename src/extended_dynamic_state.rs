use vstd::prelude::*;
use crate::pipeline::DynamicStateKind;

verus! {

//  ── Types ───────────────────────────────────────────────────────────────

///  Cull mode flags (VK_CULL_MODE_*).
pub enum CullModeFlags {
    None,
    Front,
    Back,
    FrontAndBack,
}

///  Front face winding order.
pub enum FrontFace {
    CounterClockwise,
    Clockwise,
}

///  Primitive topology for input assembly.
pub enum PrimitiveTopology {
    PointList,
    LineList,
    LineStrip,
    TriangleList,
    TriangleStrip,
    TriangleFan,
}

///  Comparison operation for depth/stencil tests.
pub enum CompareOp {
    Never,
    Less,
    Equal,
    LessOrEqual,
    Greater,
    NotEqual,
    GreaterOrEqual,
    Always,
}

///  Stencil operations.
pub enum StencilOpValue {
    Keep,
    Zero,
    Replace,
    IncrClamp,
    DecrClamp,
    Invert,
    IncrWrap,
    DecrWrap,
}

//  ── Spec Functions ──────────────────────────────────────────────────────

///  The set of all 10 extended dynamic state kinds.
pub open spec fn all_extended_dynamic_states() -> Set<DynamicStateKind> {
    set![
        DynamicStateKind::CullMode,
        DynamicStateKind::FrontFace,
        DynamicStateKind::PrimitiveTopology,
        DynamicStateKind::DepthTestEnable,
        DynamicStateKind::DepthWriteEnable,
        DynamicStateKind::DepthCompareOp,
        DynamicStateKind::DepthBoundsTestEnable,
        DynamicStateKind::StencilTestEnable,
        DynamicStateKind::StencilOp,
        DynamicStateKind::RasterizerDiscardEnable
    ]
}

///  The set of the original 9 base dynamic state kinds.
pub open spec fn base_dynamic_states() -> Set<DynamicStateKind> {
    set![
        DynamicStateKind::Viewport,
        DynamicStateKind::Scissor,
        DynamicStateKind::LineWidth,
        DynamicStateKind::DepthBias,
        DynamicStateKind::BlendConstants,
        DynamicStateKind::DepthBounds,
        DynamicStateKind::StencilCompareMask,
        DynamicStateKind::StencilWriteMask,
        DynamicStateKind::StencilReference
    ]
}

///  Whether a given set of extended dynamic states is a subset of the required states.
pub open spec fn extended_states_subset_of_required(
    states: Set<DynamicStateKind>,
    required: Set<DynamicStateKind>,
) -> bool {
    states.subset_of(required)
}

///  Whether a dynamic state kind is an extended dynamic state.
pub open spec fn is_extended_dynamic_state(kind: DynamicStateKind) -> bool {
    all_extended_dynamic_states().contains(kind)
}

///  Map a CullModeFlags to its Vulkan u32 value.
pub open spec fn cull_mode_to_vk(mode: CullModeFlags) -> u32 {
    match mode {
        CullModeFlags::None => 0u32,
        CullModeFlags::Front => 1u32,
        CullModeFlags::Back => 2u32,
        CullModeFlags::FrontAndBack => 3u32,
    }
}

///  Map a FrontFace to its Vulkan u32 value.
pub open spec fn front_face_to_vk(face: FrontFace) -> u32 {
    match face {
        FrontFace::CounterClockwise => 0u32,
        FrontFace::Clockwise => 1u32,
    }
}

///  Map a CompareOp to its Vulkan u32 value.
pub open spec fn compare_op_to_vk(op: CompareOp) -> u32 {
    match op {
        CompareOp::Never => 0u32,
        CompareOp::Less => 1u32,
        CompareOp::Equal => 2u32,
        CompareOp::LessOrEqual => 3u32,
        CompareOp::Greater => 4u32,
        CompareOp::NotEqual => 5u32,
        CompareOp::GreaterOrEqual => 6u32,
        CompareOp::Always => 7u32,
    }
}

//  ── Lemmas ──────────────────────────────────────────────────────────────

///  CullMode is an extended dynamic state.
pub proof fn lemma_cull_mode_is_extended()
    ensures is_extended_dynamic_state(DynamicStateKind::CullMode),
{
}

///  FrontFace is an extended dynamic state.
pub proof fn lemma_front_face_is_extended()
    ensures is_extended_dynamic_state(DynamicStateKind::FrontFace),
{
}

///  PrimitiveTopology is an extended dynamic state.
pub proof fn lemma_primitive_topology_is_extended()
    ensures is_extended_dynamic_state(DynamicStateKind::PrimitiveTopology),
{
}

///  Setting an extended state adds it to a set.
pub proof fn lemma_setting_state_adds_to_set(kind: DynamicStateKind, states: Set<DynamicStateKind>)
    ensures states.insert(kind).contains(kind),
{
}

} //  verus!
