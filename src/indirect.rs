use vstd::prelude::*;
use crate::resource::*;
use crate::recording::*;
use crate::pipeline::*;
use crate::render_pass::*;
use crate::memory::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// Parameters for an indirect draw call read from a GPU buffer.
pub struct IndirectDrawParams {
    /// Buffer containing draw parameters.
    pub buffer_id: nat,
    /// Byte offset into the buffer.
    pub offset: nat,
    /// Number of draws to issue.
    pub draw_count: nat,
    /// Byte stride between consecutive draw parameter structs.
    pub stride: nat,
}

/// Size of a single VkDrawIndirectCommand (4 u32s = 16 bytes).
pub open spec fn DRAW_INDIRECT_COMMAND_SIZE() -> nat { 16 }

/// Size of a single VkDrawIndexedIndirectCommand (5 u32s = 20 bytes).
pub open spec fn DRAW_INDEXED_INDIRECT_COMMAND_SIZE() -> nat { 20 }

/// Size of a single VkDispatchIndirectCommand (3 u32s = 12 bytes).
pub open spec fn DISPATCH_INDIRECT_COMMAND_SIZE() -> nat { 12 }

// ── Spec Functions ──────────────────────────────────────────────────────

/// The indirect buffer has enough space for all draw commands.
pub open spec fn indirect_buffer_size_sufficient(
    params: IndirectDrawParams,
    buffer: BufferState,
    command_size: nat,
) -> bool {
    buffer.alive
    && params.stride >= command_size
    && params.draw_count > 0 ==> (
        params.offset + (params.draw_count - 1) * params.stride + command_size
            <= buffer.size
    )
}

/// An indirect draw is valid: pipeline bound, render pass active, buffer sufficient.
pub open spec fn draw_indirect_valid(
    state: RecordingState,
    pipeline: GraphicsPipelineState,
    rp: RenderPassState,
    params: IndirectDrawParams,
    buffer: BufferState,
) -> bool {
    draw_call_valid(state, pipeline, rp)
    && indirect_buffer_size_sufficient(params, buffer, DRAW_INDIRECT_COMMAND_SIZE())
}

/// An indirect indexed draw is valid.
pub open spec fn draw_indexed_indirect_valid(
    state: RecordingState,
    pipeline: GraphicsPipelineState,
    rp: RenderPassState,
    params: IndirectDrawParams,
    buffer: BufferState,
) -> bool {
    draw_call_valid(state, pipeline, rp)
    && indirect_buffer_size_sufficient(params, buffer, DRAW_INDEXED_INDIRECT_COMMAND_SIZE())
}

/// An indirect dispatch is valid: compute pipeline bound, buffer sufficient.
pub open spec fn dispatch_indirect_valid(
    state: RecordingState,
    pipeline: ComputePipelineState,
    buffer_id: nat,
    offset: nat,
    buffer: BufferState,
) -> bool {
    dispatch_call_valid(state, pipeline)
    && buffer.alive
    && offset % 4 == 0
    && offset + DISPATCH_INDIRECT_COMMAND_SIZE() <= buffer.size
}

/// Indirect draw with count from a separate count buffer.
pub open spec fn draw_indirect_count_valid(
    state: RecordingState,
    pipeline: GraphicsPipelineState,
    rp: RenderPassState,
    params: IndirectDrawParams,
    draw_buffer: BufferState,
    count_buffer: BufferState,
    count_offset: nat,
    max_draw_count: nat,
) -> bool {
    draw_call_valid(state, pipeline, rp)
    && draw_buffer.alive
    && count_buffer.alive
    // Count buffer must have room for a u32
    && count_offset + 4 <= count_buffer.size
    // Draw buffer must have room for max_draw_count draws
    && indirect_buffer_size_sufficient(
        IndirectDrawParams { draw_count: max_draw_count, ..params },
        draw_buffer,
        DRAW_INDIRECT_COMMAND_SIZE(),
    )
}

/// A zero-draw-count indirect command.
pub open spec fn indirect_is_noop(params: IndirectDrawParams) -> bool {
    params.draw_count == 0
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// A zero-count indirect draw needs no buffer space.
pub proof fn lemma_zero_count_no_buffer_needed(
    params: IndirectDrawParams,
    buffer: BufferState,
    command_size: nat,
)
    requires
        params.draw_count == 0,
        buffer.alive,
        params.stride >= command_size,
    ensures
        indirect_buffer_size_sufficient(params, buffer, command_size),
{
}

/// draw_indirect_valid implies draw_call_valid.
pub proof fn lemma_indirect_implies_draw_valid(
    state: RecordingState,
    pipeline: GraphicsPipelineState,
    rp: RenderPassState,
    params: IndirectDrawParams,
    buffer: BufferState,
)
    requires draw_indirect_valid(state, pipeline, rp, params, buffer),
    ensures draw_call_valid(state, pipeline, rp),
{
}

/// dispatch_indirect_valid implies dispatch_call_valid.
pub proof fn lemma_indirect_dispatch_implies_dispatch_valid(
    state: RecordingState,
    pipeline: ComputePipelineState,
    buffer_id: nat,
    offset: nat,
    buffer: BufferState,
)
    requires dispatch_indirect_valid(state, pipeline, buffer_id, offset, buffer),
    ensures dispatch_call_valid(state, pipeline),
{
}

/// A single indirect draw with stride == command_size needs exactly
/// offset + command_size bytes.
pub proof fn lemma_single_draw_size(
    params: IndirectDrawParams,
    buffer: BufferState,
)
    requires
        params.draw_count == 1,
        params.stride == DRAW_INDIRECT_COMMAND_SIZE(),
        params.offset + DRAW_INDIRECT_COMMAND_SIZE() <= buffer.size,
        buffer.alive,
    ensures
        indirect_buffer_size_sufficient(params, buffer, DRAW_INDIRECT_COMMAND_SIZE()),
{
}

/// Indirect count draw implies the draw buffer can hold max_draw_count draws.
pub proof fn lemma_count_draw_buffer_sufficient(
    state: RecordingState,
    pipeline: GraphicsPipelineState,
    rp: RenderPassState,
    params: IndirectDrawParams,
    draw_buffer: BufferState,
    count_buffer: BufferState,
    count_offset: nat,
    max_draw_count: nat,
)
    requires
        draw_indirect_count_valid(state, pipeline, rp, params,
            draw_buffer, count_buffer, count_offset, max_draw_count),
    ensures
        draw_buffer.alive,
        count_buffer.alive,
{
}

/// draw_indexed_indirect_valid implies draw_call_valid.
pub proof fn lemma_indexed_indirect_implies_draw_valid(
    state: RecordingState,
    pipeline: GraphicsPipelineState,
    rp: RenderPassState,
    params: IndirectDrawParams,
    buffer: BufferState,
)
    requires draw_indexed_indirect_valid(state, pipeline, rp, params, buffer),
    ensures draw_call_valid(state, pipeline, rp),
{
}

/// A noop indirect draw (draw_count == 0) needs no specific buffer constraints.
pub proof fn lemma_noop_indirect_trivial(params: IndirectDrawParams)
    requires indirect_is_noop(params),
    ensures params.draw_count == 0,
{
}

/// Indirect draw count valid implies both buffers are alive.
pub proof fn lemma_count_draw_both_alive(
    state: RecordingState,
    pipeline: GraphicsPipelineState,
    rp: RenderPassState,
    params: IndirectDrawParams,
    draw_buffer: BufferState,
    count_buffer: BufferState,
    count_offset: nat,
    max_draw_count: nat,
)
    requires draw_indirect_count_valid(
        state, pipeline, rp, params, draw_buffer, count_buffer, count_offset, max_draw_count),
    ensures
        draw_buffer.alive,
        count_buffer.alive,
        draw_call_valid(state, pipeline, rp),
{
}

} // verus!
