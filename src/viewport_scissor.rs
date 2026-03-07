use vstd::prelude::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// A viewport transformation (maps NDC to framebuffer coordinates).
pub struct Viewport {
    pub x: int,
    pub y: int,
    pub width: nat,
    pub height: nat,
    pub min_depth: int,
    pub max_depth: int,
}

/// A scissor rectangle (clips fragments outside the rectangle).
pub struct ScissorRect {
    pub x: int,
    pub y: int,
    pub width: nat,
    pub height: nat,
}

/// Viewport/scissor state for a graphics pipeline.
pub struct ViewportScissorState {
    pub viewports: Seq<Viewport>,
    pub scissors: Seq<ScissorRect>,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// Viewport dimensions are valid (non-zero, within device limits).
pub open spec fn viewport_valid(
    vp: Viewport,
    max_width: nat,
    max_height: nat,
) -> bool {
    vp.width > 0
    && vp.height > 0
    && vp.width <= max_width
    && vp.height <= max_height
}

/// Scissor dimensions are valid (within framebuffer bounds).
pub open spec fn scissor_valid(
    scissor: ScissorRect,
    fb_width: nat,
    fb_height: nat,
) -> bool {
    scissor.x >= 0
    && scissor.y >= 0
    && (scissor.x as nat) + scissor.width <= fb_width
    && (scissor.y as nat) + scissor.height <= fb_height
}

/// Viewport and scissor counts must match.
pub open spec fn viewport_scissor_counts_match(
    state: ViewportScissorState,
) -> bool {
    state.viewports.len() == state.scissors.len()
}

/// All viewports are valid.
pub open spec fn all_viewports_valid(
    state: ViewportScissorState,
    max_width: nat,
    max_height: nat,
) -> bool {
    forall|i: int| 0 <= i < state.viewports.len()
        ==> viewport_valid(#[trigger] state.viewports[i], max_width, max_height)
}

/// All scissors are valid.
pub open spec fn all_scissors_valid(
    state: ViewportScissorState,
    fb_width: nat,
    fb_height: nat,
) -> bool {
    forall|i: int| 0 <= i < state.scissors.len()
        ==> scissor_valid(#[trigger] state.scissors[i], fb_width, fb_height)
}

/// Viewport/scissor state is well-formed.
pub open spec fn viewport_scissor_well_formed(
    state: ViewportScissorState,
    max_viewports: nat,
    max_width: nat,
    max_height: nat,
) -> bool {
    viewport_scissor_counts_match(state)
    && state.viewports.len() > 0
    && state.viewports.len() <= max_viewports
    && all_viewports_valid(state, max_width, max_height)
}

/// A single fullscreen viewport/scissor.
pub open spec fn fullscreen_viewport_scissor(
    width: nat,
    height: nat,
) -> ViewportScissorState {
    ViewportScissorState {
        viewports: seq![Viewport {
            x: 0, y: 0, width, height,
            min_depth: 0, max_depth: 1,
        }],
        scissors: seq![ScissorRect {
            x: 0, y: 0, width, height,
        }],
    }
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// Fullscreen viewport/scissor has matching counts.
pub proof fn lemma_fullscreen_counts_match(width: nat, height: nat)
    ensures
        viewport_scissor_counts_match(fullscreen_viewport_scissor(width, height)),
{
}

/// Fullscreen viewport is valid when dimensions are within limits.
pub proof fn lemma_fullscreen_viewport_valid(
    width: nat,
    height: nat,
    max_width: nat,
    max_height: nat,
)
    requires
        width > 0, height > 0,
        width <= max_width, height <= max_height,
    ensures
        all_viewports_valid(
            fullscreen_viewport_scissor(width, height),
            max_width,
            max_height,
        ),
{
}

/// Fullscreen scissor is valid when used with matching framebuffer.
pub proof fn lemma_fullscreen_scissor_valid(width: nat, height: nat)
    ensures
        all_scissors_valid(
            fullscreen_viewport_scissor(width, height),
            width,
            height,
        ),
{
}

/// A single viewport/scissor with valid dimensions is well-formed.
pub proof fn lemma_single_viewport_well_formed(
    width: nat,
    height: nat,
    max_viewports: nat,
    max_width: nat,
    max_height: nat,
)
    requires
        width > 0, height > 0,
        width <= max_width, height <= max_height,
        max_viewports >= 1,
    ensures
        viewport_scissor_well_formed(
            fullscreen_viewport_scissor(width, height),
            max_viewports,
            max_width,
            max_height,
        ),
{
}

} // verus!
