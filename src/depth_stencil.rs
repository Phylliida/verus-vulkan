use vstd::prelude::*;

verus! {

//  ── Types ───────────────────────────────────────────────────────────────

///  Comparison operator for depth/stencil tests.
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

///  Stencil operation (what to do on test pass/fail).
pub enum StencilOp {
    Keep,
    Zero,
    Replace,
    IncrementAndClamp,
    DecrementAndClamp,
    Invert,
    IncrementAndWrap,
    DecrementAndWrap,
}

///  Stencil operation state for one face (front or back).
pub struct StencilOpState {
    pub fail_op: StencilOp,
    pub pass_op: StencilOp,
    pub depth_fail_op: StencilOp,
    pub compare_op: CompareOp,
    pub compare_mask: nat,
    pub write_mask: nat,
    pub reference: nat,
}

///  Full depth/stencil state for a graphics pipeline.
pub struct DepthStencilState {
    pub depth_test_enable: bool,
    pub depth_write_enable: bool,
    pub depth_compare_op: CompareOp,
    pub depth_bounds_test_enable: bool,
    pub stencil_test_enable: bool,
    pub front: StencilOpState,
    pub back: StencilOpState,
    pub min_depth_bounds: int,
    pub max_depth_bounds: int,
}

//  ── Spec Functions ──────────────────────────────────────────────────────

///  Depth/stencil state is compatible with a render pass that has
///  a depth attachment.
pub open spec fn depth_stencil_compatible_with_attachment(
    state: DepthStencilState,
    has_depth_attachment: bool,
) -> bool {
    //  If depth test enabled, must have depth attachment
    (state.depth_test_enable ==> has_depth_attachment)
    //  If stencil test enabled, must have depth/stencil attachment
    && (state.stencil_test_enable ==> has_depth_attachment)
    //  If depth bounds test enabled, must have depth attachment
    && (state.depth_bounds_test_enable ==> has_depth_attachment)
}

///  Depth bounds are valid.
pub open spec fn depth_bounds_valid(state: DepthStencilState) -> bool {
    !state.depth_bounds_test_enable
    || state.min_depth_bounds <= state.max_depth_bounds
}

///  Depth/stencil state is well-formed.
pub open spec fn depth_stencil_well_formed(state: DepthStencilState) -> bool {
    depth_bounds_valid(state)
    //  Write enable requires test enable
    && (state.depth_write_enable ==> state.depth_test_enable)
}

///  A pipeline with no depth testing.
pub open spec fn no_depth_stencil() -> DepthStencilState {
    DepthStencilState {
        depth_test_enable: false,
        depth_write_enable: false,
        depth_compare_op: CompareOp::Always,
        depth_bounds_test_enable: false,
        stencil_test_enable: false,
        front: default_stencil_op(),
        back: default_stencil_op(),
        min_depth_bounds: 0,
        max_depth_bounds: 0,
    }
}

///  Default stencil operation state (all keep, always pass).
pub open spec fn default_stencil_op() -> StencilOpState {
    StencilOpState {
        fail_op: StencilOp::Keep,
        pass_op: StencilOp::Keep,
        depth_fail_op: StencilOp::Keep,
        compare_op: CompareOp::Always,
        compare_mask: 0xff,
        write_mask: 0xff,
        reference: 0,
    }
}

///  Depth test with less-than comparison (most common).
pub open spec fn depth_test_less() -> DepthStencilState {
    DepthStencilState {
        depth_test_enable: true,
        depth_write_enable: true,
        depth_compare_op: CompareOp::Less,
        depth_bounds_test_enable: false,
        stencil_test_enable: false,
        front: default_stencil_op(),
        back: default_stencil_op(),
        min_depth_bounds: 0,
        max_depth_bounds: 0,
    }
}

//  ── Proofs ──────────────────────────────────────────────────────────────

///  No depth/stencil is well-formed.
pub proof fn lemma_no_depth_stencil_well_formed()
    ensures depth_stencil_well_formed(no_depth_stencil()),
{
}

///  No depth/stencil is compatible with any attachment configuration.
pub proof fn lemma_no_depth_stencil_always_compatible(has_depth: bool)
    ensures
        depth_stencil_compatible_with_attachment(no_depth_stencil(), has_depth),
{
}

///  Standard depth-less test is well-formed.
pub proof fn lemma_depth_test_less_well_formed()
    ensures depth_stencil_well_formed(depth_test_less()),
{
}

///  Standard depth-less test requires a depth attachment.
pub proof fn lemma_depth_test_less_needs_attachment()
    ensures
        depth_stencil_compatible_with_attachment(depth_test_less(), true),
        !depth_stencil_compatible_with_attachment(depth_test_less(), false),
{
}

///  Depth write without test is not well-formed.
pub proof fn lemma_write_without_test_malformed()
    ensures !depth_stencil_well_formed(DepthStencilState {
        depth_test_enable: false,
        depth_write_enable: true,
        depth_compare_op: CompareOp::Less,
        depth_bounds_test_enable: false,
        stencil_test_enable: false,
        front: default_stencil_op(),
        back: default_stencil_op(),
        min_depth_bounds: 0,
        max_depth_bounds: 0,
    }),
{
}

} //  verus!
