use vstd::prelude::*;
use crate::recording::*;
use crate::resource::*;
use crate::flags::*;
use crate::sync::*;
use crate::sync_token::*;
use crate::pool_ownership::*;
use crate::pipeline::*;
use crate::render_pass::*;
use crate::draw_state::{DrawCallState, dynamic_states_satisfied,
    vertex_draw_in_bounds, indexed_draw_in_bounds};
use crate::image_layout::ImageLayout;
use crate::image_layout_fsm::*;
use crate::framebuffer::*;
use crate::memory::*;
use crate::lifetime::*;
use crate::indirect::*;
use crate::dynamic_rendering::*;
use super::image_layout::RuntimeImageLayoutTracker;
use super::device::RuntimeDevice;
use crate::vk_context::VulkanContext;

verus! {

/// Recording state of a command buffer.
pub enum CommandBufferStatus {
    /// Initial or reset state.
    Initial,
    /// Between begin and end.
    Recording,
    /// Recorded, ready for submission.
    Executable,
    /// Submitted to a queue; pending GPU execution.
    Pending,
}

/// Runtime wrapper for a Vulkan command buffer.
pub struct RuntimeCommandBuffer {
    /// Opaque handle (maps to VkCommandBuffer).
    pub handle: u64,
    /// Ghost logical ID for sync token tracking.
    pub cb_id: Ghost<nat>,
    /// Current status.
    pub status: Ghost<CommandBufferStatus>,
    /// Recorded barrier log (ghost).
    pub barrier_log: Ghost<BarrierLog>,
    /// Whether we are inside a render pass.
    pub in_render_pass: Ghost<bool>,
    /// Ghost recording state: tracks bound pipelines, descriptor sets, and active render pass.
    pub recording_state: Ghost<RecordingState>,
    /// Ghost thread that began recording this command buffer.
    pub recording_thread: Ghost<ThreadId>,
}

/// Well-formedness of the runtime command buffer.
/// The in_render_pass field must be consistent with the recording state.
pub open spec fn runtime_cb_wf(cb: &RuntimeCommandBuffer) -> bool {
    cb.in_render_pass@ == in_render_pass(cb.recording_state@)
}

/// Image is in a valid layout for being a transfer source.
pub open spec fn valid_transfer_src_layout(layout: ImageLayout) -> bool {
    layout == ImageLayout::TransferSrcOptimal || layout == ImageLayout::General
}

/// Image is in a valid layout for being a transfer destination.
pub open spec fn valid_transfer_dst_layout(layout: ImageLayout) -> bool {
    layout == ImageLayout::TransferDstOptimal || layout == ImageLayout::General
}

/// Command buffer is in recording state.
pub open spec fn is_recording(cb: &RuntimeCommandBuffer) -> bool {
    match cb.status@ {
        CommandBufferStatus::Recording => true,
        _ => false,
    }
}

/// Command buffer is executable.
pub open spec fn is_executable(cb: &RuntimeCommandBuffer) -> bool {
    match cb.status@ {
        CommandBufferStatus::Executable => true,
        _ => false,
    }
}

/// Command buffer is pending (submitted, awaiting GPU completion).
pub open spec fn is_pending(cb: &RuntimeCommandBuffer) -> bool {
    match cb.status@ {
        CommandBufferStatus::Pending => true,
        _ => false,
    }
}

/// Exec: begin recording.
/// Caller must prove exclusive access to the CB via pool ownership or direct token.
pub fn begin_recording_exec(
    ctx: &VulkanContext,
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
    pool: Ghost<PoolOwnership>,
    reg: Ghost<TokenRegistry>,
)
    requires
        is_initial(&*old(cb)) || is_executable(&*old(cb)),
        can_access_child(pool@, old(cb).cb_id@, thread@, reg@),
    ensures
        is_recording(cb),
        cb.barrier_log@ == Seq::<BarrierEntry>::empty(),
        cb.in_render_pass@ == false,
        cb.recording_state@ == initial_recording_state(),
        cb.recording_thread@ == thread@,
        cb.cb_id@ == old(cb).cb_id@,
        runtime_cb_wf(cb),
{
    crate::ffi::ffi_begin_command_buffer(ctx, cb.handle);
    cb.status = Ghost(CommandBufferStatus::Recording);
    cb.barrier_log = Ghost(Seq::empty());
    cb.in_render_pass = Ghost(false);
    cb.recording_state = Ghost(initial_recording_state());
    cb.recording_thread = thread;
}

/// Exec: end recording.
/// Must be called by the same thread that began recording, with pool access.
pub fn end_recording_exec(
    ctx: &VulkanContext,
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
    pool: Ghost<PoolOwnership>,
    reg: Ghost<TokenRegistry>,
)
    requires
        is_recording(&*old(cb)),
        runtime_cb_wf(&*old(cb)),
        old(cb).in_render_pass@ == false,
        can_access_child(pool@, old(cb).cb_id@, thread@, reg@),
        old(cb).recording_thread@ == thread@,
    ensures
        is_executable(cb),
        cb.recording_state@ == old(cb).recording_state@,
        cb.in_render_pass@ == old(cb).in_render_pass@,
        cb.recording_thread@ == old(cb).recording_thread@,
        cb.cb_id@ == old(cb).cb_id@,
        runtime_cb_wf(cb),
{
    crate::ffi::ffi_end_command_buffer(ctx, cb.handle);
    cb.status = Ghost(CommandBufferStatus::Executable);
}

/// Exec: begin render pass.
/// Caller must prove the framebuffer is compatible with the render pass
/// and that attachment images are in their expected initial layouts.
pub fn cmd_begin_render_pass_exec(
    ctx: &VulkanContext,
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
    rp_handle: u64,
    fb_handle: u64,
    width: u32,
    height: u32,
    rp: Ghost<RenderPassState>,
    fb: Ghost<FramebufferState>,
    layout_tracker: &RuntimeImageLayoutTracker,
    attachment_resources: Ghost<Seq<ResourceId>>,
)
    requires
        is_recording(&*old(cb)),
        runtime_cb_wf(&*old(cb)),
        old(cb).in_render_pass@ == false,
        old(cb).recording_thread@ == thread@,
        rp@.alive,
        fb@.alive,
        framebuffer_compatible_with_render_pass(fb@, rp@),
        attachment_resources@.len() == rp@.attachments.len(),
        attachments_match_initial_layouts(layout_tracker@, rp@, attachment_resources@),
    ensures
        is_recording(cb),
        cb.in_render_pass@ == true,
        cb.recording_state@ == begin_render_pass_recording(old(cb).recording_state@, rp@.id, fb@.id),
        cb.barrier_log@ == old(cb).barrier_log@,
        cb.recording_thread@ == old(cb).recording_thread@,
        cb.cb_id@ == old(cb).cb_id@,
        runtime_cb_wf(cb),
{
    crate::ffi::ffi_cmd_begin_render_pass(ctx, cb.handle, rp_handle, fb_handle, width, height);
    cb.in_render_pass = Ghost(true);
    cb.recording_state = Ghost(begin_render_pass_recording(cb.recording_state@, rp@.id, fb@.id));
}

/// Exec: end render pass.
/// Updates the layout tracker so each attachment is in its final_layout.
pub fn cmd_end_render_pass_exec(
    ctx: &VulkanContext,
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
    rp: Ghost<RenderPassState>,
    attachment_resources: Ghost<Seq<ResourceId>>,
    layout_tracker: &mut RuntimeImageLayoutTracker,
)
    requires
        is_recording(&*old(cb)),
        runtime_cb_wf(&*old(cb)),
        old(cb).in_render_pass@ == true,
        old(cb).recording_thread@ == thread@,
        attachment_resources@.len() == rp@.attachments.len(),
        render_pass_well_formed(rp@),
    ensures
        is_recording(cb),
        cb.in_render_pass@ == false,
        cb.recording_state@ == end_render_pass_recording(old(cb).recording_state@),
        cb.barrier_log@ == old(cb).barrier_log@,
        cb.recording_thread@ == old(cb).recording_thread@,
        cb.cb_id@ == old(cb).cb_id@,
        runtime_cb_wf(cb),
        layout_tracker@ == apply_transitions(
            old(layout_tracker)@,
            render_pass_end_transitions(rp@, attachment_resources@),
        ),
{
    crate::ffi::ffi_cmd_end_render_pass(ctx, cb.handle);
    cb.in_render_pass = Ghost(false);
    cb.recording_state = Ghost(end_render_pass_recording(cb.recording_state@));
    layout_tracker.states = Ghost(apply_transitions(
        layout_tracker.states@,
        render_pass_end_transitions(rp@, attachment_resources@),
    ));
}

/// Exec: advance to the next subpass within a render pass.
/// Caller must prove the next subpass exists in the render pass.
pub fn cmd_next_subpass_exec(
    ctx: &VulkanContext,
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
    rp: Ghost<RenderPassState>,
)
    requires
        is_recording(&*old(cb)),
        runtime_cb_wf(&*old(cb)),
        old(cb).in_render_pass@ == true,
        old(cb).recording_thread@ == thread@,
        old(cb).recording_state@.active_render_pass.is_some(),
        old(cb).recording_state@.active_render_pass.unwrap().render_pass_id == rp@.id,
        old(cb).recording_state@.active_render_pass.unwrap().subpass_index + 1 < rp@.subpasses.len(),
    ensures
        is_recording(cb),
        cb.in_render_pass@ == true,
        cb.recording_state@ == next_subpass_recording(old(cb).recording_state@),
        cb.barrier_log@ == old(cb).barrier_log@,
        cb.recording_thread@ == old(cb).recording_thread@,
        cb.cb_id@ == old(cb).cb_id@,
        runtime_cb_wf(cb),
{
    crate::ffi::ffi_cmd_next_subpass(ctx, cb.handle);
    cb.recording_state = Ghost(next_subpass_recording(cb.recording_state@));
}

/// Exec: record a pipeline barrier.
/// The runtime stage bitmasks must match the ghost barrier entry's stage sets.
pub fn cmd_pipeline_barrier_exec(
    ctx: &VulkanContext,
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
    src_stage: u32,
    dst_stage: u32,
    entry: Ghost<BarrierEntry>,
)
    requires
        is_recording(&*old(cb)),
        runtime_cb_wf(&*old(cb)),
        old(cb).recording_thread@ == thread@,
        src_stage == stages_to_vk_bitmask(entry@.src_stages),
        dst_stage == stages_to_vk_bitmask(entry@.dst_stages),
    ensures
        is_recording(cb),
        cb.barrier_log@ == old(cb).barrier_log@.push(entry@),
        cb.recording_state@ == old(cb).recording_state@,
        cb.in_render_pass@ == old(cb).in_render_pass@,
        cb.recording_thread@ == old(cb).recording_thread@,
        cb.cb_id@ == old(cb).cb_id@,
        runtime_cb_wf(cb),
{
    crate::ffi::ffi_cmd_pipeline_barrier(ctx, cb.handle, src_stage, dst_stage);
    cb.barrier_log = Ghost(cb.barrier_log@.push(entry@));
}

/// Exec: bind a graphics pipeline (updates recording state).
/// Caller must prove the pipeline is alive and the id matches.
pub fn cmd_bind_graphics_pipeline_exec(
    ctx: &VulkanContext,
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
    pipeline_handle: u64,
    pipeline_id: Ghost<nat>,
    pipeline: Ghost<GraphicsPipelineState>,
)
    requires
        is_recording(&*old(cb)),
        runtime_cb_wf(&*old(cb)),
        old(cb).recording_thread@ == thread@,
        pipeline@.alive,
        pipeline@.id == pipeline_id@,
    ensures
        is_recording(cb),
        cb.barrier_log@ == old(cb).barrier_log@,
        cb.recording_state@ == bind_graphics_pipeline(old(cb).recording_state@, pipeline_id@),
        cb.in_render_pass@ == old(cb).in_render_pass@,
        cb.recording_thread@ == old(cb).recording_thread@,
        cb.cb_id@ == old(cb).cb_id@,
        runtime_cb_wf(cb),
{
    crate::ffi::ffi_cmd_bind_pipeline(ctx, cb.handle, 0, pipeline_handle);
    cb.recording_state = Ghost(bind_graphics_pipeline(cb.recording_state@, pipeline_id@));
}

/// Exec: bind a compute pipeline (updates recording state).
/// Caller must prove the pipeline is alive and the id matches.
pub fn cmd_bind_compute_pipeline_exec(
    ctx: &VulkanContext,
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
    pipeline_handle: u64,
    pipeline_id: Ghost<nat>,
    pipeline: Ghost<ComputePipelineState>,
)
    requires
        is_recording(&*old(cb)),
        runtime_cb_wf(&*old(cb)),
        old(cb).recording_thread@ == thread@,
        pipeline@.alive,
        pipeline@.id == pipeline_id@,
    ensures
        is_recording(cb),
        cb.barrier_log@ == old(cb).barrier_log@,
        cb.recording_state@ == bind_compute_pipeline(old(cb).recording_state@, pipeline_id@),
        cb.in_render_pass@ == old(cb).in_render_pass@,
        cb.recording_thread@ == old(cb).recording_thread@,
        cb.cb_id@ == old(cb).cb_id@,
        runtime_cb_wf(cb),
{
    crate::ffi::ffi_cmd_bind_pipeline(ctx, cb.handle, 1, pipeline_handle);
    cb.recording_state = Ghost(bind_compute_pipeline(cb.recording_state@, pipeline_id@));
}

/// Exec: bind a pipeline (backward compat, delegates to graphics variant).
/// Caller must prove the pipeline is alive and the id matches.
pub fn cmd_bind_pipeline_exec(
    ctx: &VulkanContext,
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
    pipeline_handle: u64,
    pipeline_id: Ghost<nat>,
    pipeline: Ghost<GraphicsPipelineState>,
)
    requires
        is_recording(&*old(cb)),
        runtime_cb_wf(&*old(cb)),
        old(cb).recording_thread@ == thread@,
        pipeline@.alive,
        pipeline@.id == pipeline_id@,
    ensures
        is_recording(cb),
        cb.barrier_log@ == old(cb).barrier_log@,
        cb.recording_state@ == bind_graphics_pipeline(old(cb).recording_state@, pipeline_id@),
        cb.in_render_pass@ == old(cb).in_render_pass@,
        cb.recording_thread@ == old(cb).recording_thread@,
        cb.cb_id@ == old(cb).cb_id@,
        runtime_cb_wf(cb),
{
    crate::ffi::ffi_cmd_bind_pipeline(ctx, cb.handle, 0, pipeline_handle);
    cb.recording_state = Ghost(bind_graphics_pipeline(cb.recording_state@, pipeline_id@));
}

/// Exec: bind a descriptor set at a given set index.
/// The layout_id must match the descriptor set's actual layout for pipeline compatibility.
/// Dynamic offsets are stored for later validation against buffer bounds.
pub fn cmd_bind_descriptor_set_exec(
    ctx: &VulkanContext,
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
    bind_point: u32,
    layout_handle: u64,
    first_set: u32,
    set_handles: &[u64],
    set_index: Ghost<nat>,
    set_id: Ghost<nat>,
    layout_id: Ghost<nat>,
    dynamic_offsets: Ghost<Seq<nat>>,
)
    requires
        is_recording(&*old(cb)),
        runtime_cb_wf(&*old(cb)),
        old(cb).recording_thread@ == thread@,
    ensures
        is_recording(cb),
        cb.barrier_log@ == old(cb).barrier_log@,
        cb.recording_state@ == bind_descriptor_set(old(cb).recording_state@, set_index@, set_id@, layout_id@, dynamic_offsets@),
        cb.in_render_pass@ == old(cb).in_render_pass@,
        cb.recording_thread@ == old(cb).recording_thread@,
        cb.cb_id@ == old(cb).cb_id@,
        runtime_cb_wf(cb),
{
    crate::ffi::ffi_cmd_bind_descriptor_sets(ctx, cb.handle, bind_point, layout_handle, first_set, set_handles);
    cb.recording_state = Ghost(bind_descriptor_set(cb.recording_state@, set_index@, set_id@, layout_id@, dynamic_offsets@));
}

/// Exec: bind a vertex buffer at a given slot.
/// Caller must prove the buffer is alive and the id matches.
pub fn cmd_bind_vertex_buffer_exec(
    ctx: &VulkanContext,
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
    first_binding: u32,
    buffer_handle: u64,
    offset: u64,
    slot: Ghost<nat>,
    buffer_id: Ghost<nat>,
    buffer: Ghost<BufferState>,
)
    requires
        is_recording(&*old(cb)),
        runtime_cb_wf(&*old(cb)),
        old(cb).recording_thread@ == thread@,
        buffer@.alive,
        buffer@.id == buffer_id@,
    ensures
        is_recording(cb),
        cb.barrier_log@ == old(cb).barrier_log@,
        cb.recording_state@ == bind_vertex_buffer(old(cb).recording_state@, slot@, buffer_id@),
        cb.in_render_pass@ == old(cb).in_render_pass@,
        cb.recording_thread@ == old(cb).recording_thread@,
        cb.cb_id@ == old(cb).cb_id@,
        runtime_cb_wf(cb),
{
    crate::ffi::ffi_cmd_bind_vertex_buffers(ctx, cb.handle, first_binding, buffer_handle, offset);
    cb.recording_state = Ghost(bind_vertex_buffer(cb.recording_state@, slot@, buffer_id@));
}

/// Exec: bind an index buffer.
/// Caller must prove the buffer is alive and the id matches.
pub fn cmd_bind_index_buffer_exec(
    ctx: &VulkanContext,
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
    buffer_handle: u64,
    offset: u64,
    index_type: u32,
    buffer_id: Ghost<nat>,
    buffer: Ghost<BufferState>,
)
    requires
        is_recording(&*old(cb)),
        runtime_cb_wf(&*old(cb)),
        old(cb).recording_thread@ == thread@,
        buffer@.alive,
        buffer@.id == buffer_id@,
    ensures
        is_recording(cb),
        cb.barrier_log@ == old(cb).barrier_log@,
        cb.recording_state@ == bind_index_buffer(old(cb).recording_state@, buffer_id@),
        cb.in_render_pass@ == old(cb).in_render_pass@,
        cb.recording_thread@ == old(cb).recording_thread@,
        cb.cb_id@ == old(cb).cb_id@,
        runtime_cb_wf(cb),
{
    crate::ffi::ffi_cmd_bind_index_buffer(ctx, cb.handle, buffer_handle, offset, index_type);
    cb.recording_state = Ghost(bind_index_buffer(cb.recording_state@, buffer_id@));
}

/// Exec: set the dynamic viewport.
pub fn cmd_set_viewport_exec(
    ctx: &VulkanContext,
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
    x: f32,
    y: f32,
    w: f32,
    h: f32,
    min_d: f32,
    max_d: f32,
)
    requires
        is_recording(&*old(cb)),
        runtime_cb_wf(&*old(cb)),
        old(cb).recording_thread@ == thread@,
    ensures
        is_recording(cb),
        cb.barrier_log@ == old(cb).barrier_log@,
        cb.recording_state@ == set_viewport_recording(old(cb).recording_state@),
        cb.in_render_pass@ == old(cb).in_render_pass@,
        cb.recording_thread@ == old(cb).recording_thread@,
        cb.cb_id@ == old(cb).cb_id@,
        runtime_cb_wf(cb),
{
    crate::ffi::ffi_cmd_set_viewport(ctx, cb.handle, x, y, w, h, min_d, max_d);
    cb.recording_state = Ghost(set_viewport_recording(cb.recording_state@));
}

/// Exec: set the dynamic scissor.
pub fn cmd_set_scissor_exec(
    ctx: &VulkanContext,
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
    x: i32,
    y: i32,
    w: u32,
    h: u32,
)
    requires
        is_recording(&*old(cb)),
        runtime_cb_wf(&*old(cb)),
        old(cb).recording_thread@ == thread@,
    ensures
        is_recording(cb),
        cb.barrier_log@ == old(cb).barrier_log@,
        cb.recording_state@ == set_scissor_recording(old(cb).recording_state@),
        cb.in_render_pass@ == old(cb).in_render_pass@,
        cb.recording_thread@ == old(cb).recording_thread@,
        cb.cb_id@ == old(cb).cb_id@,
        runtime_cb_wf(cb),
{
    crate::ffi::ffi_cmd_set_scissor(ctx, cb.handle, x, y, w, h);
    cb.recording_state = Ghost(set_scissor_recording(cb.recording_state@));
}

/// Exec: set push constants.
pub fn cmd_set_push_constants_exec(
    ctx: &VulkanContext,
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
    layout_handle: u64,
    stage_flags: u32,
    offset: u32,
    data: &[u8],
)
    requires
        is_recording(&*old(cb)),
        runtime_cb_wf(&*old(cb)),
        old(cb).recording_thread@ == thread@,
    ensures
        is_recording(cb),
        cb.barrier_log@ == old(cb).barrier_log@,
        cb.recording_state@ == set_push_constants_recording(old(cb).recording_state@),
        cb.in_render_pass@ == old(cb).in_render_pass@,
        cb.recording_thread@ == old(cb).recording_thread@,
        cb.cb_id@ == old(cb).cb_id@,
        runtime_cb_wf(cb),
{
    crate::ffi::ffi_cmd_push_constants(ctx, cb.handle, layout_handle, stage_flags, offset, data);
    cb.recording_state = Ghost(set_push_constants_recording(cb.recording_state@));
}

/// Exec: record a draw command.
/// Caller must prove: pipeline bound, descriptors bound, vertex buffer bound,
/// all required dynamic states set, and vertex draw in bounds.
pub fn cmd_draw_exec(
    ctx: &VulkanContext,
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
    vertex_count: u32,
    instance_count: u32,
    first_vertex: u32,
    first_instance: u32,
    pipeline: Ghost<GraphicsPipelineState>,
    rp: Ghost<RenderPassState>,
    draw_state: Ghost<DrawCallState>,
    required_vertex_slots: Ghost<Set<nat>>,
)
    requires
        is_recording(&*old(cb)),
        runtime_cb_wf(&*old(cb)),
        old(cb).in_render_pass@ == true,
        old(cb).recording_thread@ == thread@,
        pipeline@.alive,
        rp@.alive,
        draw_call_valid(old(cb).recording_state@, pipeline@, rp@),
        descriptor_sets_bound_for_pipeline(old(cb).recording_state@, pipeline@.descriptor_set_layouts),
        has_vertex_buffer_bound(old(cb).recording_state@),
        dynamic_states_satisfied(draw_state@, pipeline@.required_dynamic_states),
        vertex_draw_in_bounds(draw_state@, required_vertex_slots@, first_vertex as nat, vertex_count as nat),
    ensures
        is_recording(cb),
        cb.barrier_log@ == old(cb).barrier_log@,
        cb.recording_state@ == old(cb).recording_state@,
        cb.in_render_pass@ == old(cb).in_render_pass@,
        cb.recording_thread@ == old(cb).recording_thread@,
        cb.cb_id@ == old(cb).cb_id@,
        runtime_cb_wf(cb),
{
    crate::ffi::ffi_cmd_draw(ctx, cb.handle, vertex_count, instance_count, first_vertex, first_instance);
}

/// Exec: record an indexed draw command.
/// Same as cmd_draw_exec but additionally requires index buffer bound + index bounds.
pub fn cmd_draw_indexed_exec(
    ctx: &VulkanContext,
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
    index_count: u32,
    instance_count: u32,
    first_index: u32,
    vertex_offset: i32,
    first_instance: u32,
    pipeline: Ghost<GraphicsPipelineState>,
    rp: Ghost<RenderPassState>,
    draw_state: Ghost<DrawCallState>,
    required_vertex_slots: Ghost<Set<nat>>,
    first_vertex_ghost: Ghost<nat>,
    vertex_count_ghost: Ghost<nat>,
)
    requires
        is_recording(&*old(cb)),
        runtime_cb_wf(&*old(cb)),
        old(cb).in_render_pass@ == true,
        old(cb).recording_thread@ == thread@,
        pipeline@.alive,
        rp@.alive,
        draw_call_valid(old(cb).recording_state@, pipeline@, rp@),
        descriptor_sets_bound_for_pipeline(old(cb).recording_state@, pipeline@.descriptor_set_layouts),
        has_vertex_buffer_bound(old(cb).recording_state@),
        has_index_buffer_bound(old(cb).recording_state@),
        dynamic_states_satisfied(draw_state@, pipeline@.required_dynamic_states),
        vertex_draw_in_bounds(draw_state@, required_vertex_slots@, first_vertex_ghost@, vertex_count_ghost@),
        indexed_draw_in_bounds(draw_state@, first_index as nat, index_count as nat),
    ensures
        is_recording(cb),
        cb.barrier_log@ == old(cb).barrier_log@,
        cb.recording_state@ == old(cb).recording_state@,
        cb.in_render_pass@ == old(cb).in_render_pass@,
        cb.recording_thread@ == old(cb).recording_thread@,
        cb.cb_id@ == old(cb).cb_id@,
        runtime_cb_wf(cb),
{
    crate::ffi::ffi_cmd_draw_indexed(ctx, cb.handle, index_count, instance_count, first_index, vertex_offset, first_instance);
}

/// Exec: record a dispatch command.
/// Caller must prove a compatible compute pipeline is bound and all descriptor sets are bound.
pub fn cmd_dispatch_exec(
    ctx: &VulkanContext,
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
    group_count_x: u32,
    group_count_y: u32,
    group_count_z: u32,
    pipeline: Ghost<ComputePipelineState>,
)
    requires
        is_recording(&*old(cb)),
        runtime_cb_wf(&*old(cb)),
        old(cb).in_render_pass@ == false,
        old(cb).recording_thread@ == thread@,
        pipeline@.alive,
        dispatch_call_valid(old(cb).recording_state@, pipeline@),
        descriptor_sets_bound_for_pipeline(old(cb).recording_state@, pipeline@.descriptor_set_layouts),
    ensures
        is_recording(cb),
        cb.barrier_log@ == old(cb).barrier_log@,
        cb.recording_state@ == old(cb).recording_state@,
        cb.in_render_pass@ == old(cb).in_render_pass@,
        cb.recording_thread@ == old(cb).recording_thread@,
        cb.cb_id@ == old(cb).cb_id@,
        runtime_cb_wf(cb),
{
    crate::ffi::ffi_cmd_dispatch(ctx, cb.handle, group_count_x, group_count_y, group_count_z);
}

/// Exec: record a buffer-to-buffer copy.
/// Transfer commands must be outside a render pass.
/// Caller must prove source is readable and destination is writable at the transfer stage.
pub fn cmd_copy_buffer_exec(
    ctx: &VulkanContext,
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
    src_handle: u64,
    dst_handle: u64,
    size: u64,
    src_buffer: Ghost<nat>,
    dst_buffer: Ghost<nat>,
    src_sync: Ghost<SyncState>,
    dst_sync: Ghost<SyncState>,
)
    requires
        is_recording(&*old(cb)),
        runtime_cb_wf(&*old(cb)),
        old(cb).in_render_pass@ == false,
        old(cb).recording_thread@ == thread@,
        src_buffer@ != dst_buffer@,
        readable(old(cb).barrier_log@, src_sync@, STAGE_TRANSFER(), ACCESS_TRANSFER_READ()),
        writable(old(cb).barrier_log@, dst_sync@, STAGE_TRANSFER(), ACCESS_TRANSFER_WRITE()),
    ensures
        is_recording(cb),
        cb.barrier_log@ == old(cb).barrier_log@,
        cb.recording_state@ == old(cb).recording_state@,
        cb.in_render_pass@ == old(cb).in_render_pass@,
        cb.recording_thread@ == old(cb).recording_thread@,
        cb.cb_id@ == old(cb).cb_id@,
        runtime_cb_wf(cb),
{
    crate::ffi::ffi_cmd_copy_buffer(ctx, cb.handle, src_handle, dst_handle, size);
}

/// Exec: record an image-to-image copy.
/// Transfer commands must be outside a render pass.
/// Source must be in TransferSrcOptimal or General; dest must be in TransferDstOptimal or General.
/// Caller must prove source is readable and destination is writable at the transfer stage.
pub fn cmd_copy_image_exec(
    ctx: &VulkanContext,
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
    src_img_handle: u64,
    dst_img_handle: u64,
    width: u32,
    height: u32,
    layout_tracker: &RuntimeImageLayoutTracker,
    src_image: Ghost<ResourceId>,
    dst_image: Ghost<ResourceId>,
    src_sync: Ghost<SyncState>,
    dst_sync: Ghost<SyncState>,
)
    requires
        is_recording(&*old(cb)),
        runtime_cb_wf(&*old(cb)),
        old(cb).in_render_pass@ == false,
        old(cb).recording_thread@ == thread@,
        src_image@ != dst_image@,
        layout_tracker@.contains_key(src_image@),
        layout_tracker@.contains_key(dst_image@),
        valid_transfer_src_layout(layout_tracker@[src_image@]),
        valid_transfer_dst_layout(layout_tracker@[dst_image@]),
        readable(old(cb).barrier_log@, src_sync@, STAGE_TRANSFER(), ACCESS_TRANSFER_READ()),
        writable(old(cb).barrier_log@, dst_sync@, STAGE_TRANSFER(), ACCESS_TRANSFER_WRITE()),
    ensures
        is_recording(cb),
        cb.barrier_log@ == old(cb).barrier_log@,
        cb.recording_state@ == old(cb).recording_state@,
        cb.in_render_pass@ == old(cb).in_render_pass@,
        cb.recording_thread@ == old(cb).recording_thread@,
        cb.cb_id@ == old(cb).cb_id@,
        runtime_cb_wf(cb),
{
    crate::ffi::ffi_cmd_copy_image(ctx, cb.handle, src_img_handle, dst_img_handle, width, height);
}

/// Exec: record an image blit (scaled copy).
/// Transfer commands must be outside a render pass.
/// Source must be in TransferSrcOptimal or General; dest must be in TransferDstOptimal or General.
/// Caller must prove source is readable and destination is writable at the transfer stage.
pub fn cmd_blit_image_exec(
    ctx: &VulkanContext,
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
    src_img_handle: u64,
    dst_img_handle: u64,
    width: u32,
    height: u32,
    layout_tracker: &RuntimeImageLayoutTracker,
    src_image: Ghost<ResourceId>,
    dst_image: Ghost<ResourceId>,
    src_sync: Ghost<SyncState>,
    dst_sync: Ghost<SyncState>,
)
    requires
        is_recording(&*old(cb)),
        runtime_cb_wf(&*old(cb)),
        old(cb).in_render_pass@ == false,
        old(cb).recording_thread@ == thread@,
        src_image@ != dst_image@,
        layout_tracker@.contains_key(src_image@),
        layout_tracker@.contains_key(dst_image@),
        valid_transfer_src_layout(layout_tracker@[src_image@]),
        valid_transfer_dst_layout(layout_tracker@[dst_image@]),
        readable(old(cb).barrier_log@, src_sync@, STAGE_TRANSFER(), ACCESS_TRANSFER_READ()),
        writable(old(cb).barrier_log@, dst_sync@, STAGE_TRANSFER(), ACCESS_TRANSFER_WRITE()),
    ensures
        is_recording(cb),
        cb.barrier_log@ == old(cb).barrier_log@,
        cb.recording_state@ == old(cb).recording_state@,
        cb.in_render_pass@ == old(cb).in_render_pass@,
        cb.recording_thread@ == old(cb).recording_thread@,
        cb.cb_id@ == old(cb).cb_id@,
        runtime_cb_wf(cb),
{
    crate::ffi::ffi_cmd_blit_image(ctx, cb.handle, src_img_handle, dst_img_handle, width, height);
}

/// Exec: record a buffer-to-image copy.
/// Transfer commands must be outside a render pass.
/// Dest image must be in TransferDstOptimal or General.
/// Caller must prove source buffer is readable and destination image is writable.
pub fn cmd_copy_buffer_to_image_exec(
    ctx: &VulkanContext,
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
    src_buf_handle: u64,
    dst_img_handle: u64,
    width: u32,
    height: u32,
    layout_tracker: &RuntimeImageLayoutTracker,
    src_buffer: Ghost<nat>,
    dst_image: Ghost<ResourceId>,
    src_sync: Ghost<SyncState>,
    dst_sync: Ghost<SyncState>,
)
    requires
        is_recording(&*old(cb)),
        runtime_cb_wf(&*old(cb)),
        old(cb).in_render_pass@ == false,
        old(cb).recording_thread@ == thread@,
        layout_tracker@.contains_key(dst_image@),
        valid_transfer_dst_layout(layout_tracker@[dst_image@]),
        readable(old(cb).barrier_log@, src_sync@, STAGE_TRANSFER(), ACCESS_TRANSFER_READ()),
        writable(old(cb).barrier_log@, dst_sync@, STAGE_TRANSFER(), ACCESS_TRANSFER_WRITE()),
    ensures
        is_recording(cb),
        cb.barrier_log@ == old(cb).barrier_log@,
        cb.recording_state@ == old(cb).recording_state@,
        cb.in_render_pass@ == old(cb).in_render_pass@,
        cb.recording_thread@ == old(cb).recording_thread@,
        cb.cb_id@ == old(cb).cb_id@,
        runtime_cb_wf(cb),
{
    crate::ffi::ffi_cmd_copy_buffer_to_image(ctx, cb.handle, src_buf_handle, dst_img_handle, width, height);
}

/// Exec: record an image-to-buffer copy.
/// Transfer commands must be outside a render pass.
/// Source image must be in TransferSrcOptimal or General.
/// Caller must prove source image is readable and destination buffer is writable.
pub fn cmd_copy_image_to_buffer_exec(
    ctx: &VulkanContext,
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
    src_img_handle: u64,
    dst_buf_handle: u64,
    width: u32,
    height: u32,
    layout_tracker: &RuntimeImageLayoutTracker,
    src_image: Ghost<ResourceId>,
    dst_buffer: Ghost<nat>,
    src_sync: Ghost<SyncState>,
    dst_sync: Ghost<SyncState>,
)
    requires
        is_recording(&*old(cb)),
        runtime_cb_wf(&*old(cb)),
        old(cb).in_render_pass@ == false,
        old(cb).recording_thread@ == thread@,
        layout_tracker@.contains_key(src_image@),
        valid_transfer_src_layout(layout_tracker@[src_image@]),
        readable(old(cb).barrier_log@, src_sync@, STAGE_TRANSFER(), ACCESS_TRANSFER_READ()),
        writable(old(cb).barrier_log@, dst_sync@, STAGE_TRANSFER(), ACCESS_TRANSFER_WRITE()),
    ensures
        is_recording(cb),
        cb.barrier_log@ == old(cb).barrier_log@,
        cb.recording_state@ == old(cb).recording_state@,
        cb.in_render_pass@ == old(cb).in_render_pass@,
        cb.recording_thread@ == old(cb).recording_thread@,
        cb.cb_id@ == old(cb).cb_id@,
        runtime_cb_wf(cb),
{
    crate::ffi::ffi_cmd_copy_image_to_buffer(ctx, cb.handle, src_img_handle, dst_buf_handle, width, height);
}

/// Exec: record an indirect draw command.
/// Caller must prove: pipeline bound, in render pass, indirect buffer sufficient.
pub fn cmd_draw_indirect_exec(
    ctx: &VulkanContext,
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
    buffer_handle: u64,
    offset: u64,
    draw_count: u32,
    stride: u32,
    pipeline: Ghost<GraphicsPipelineState>,
    rp: Ghost<RenderPassState>,
    draw_state: Ghost<DrawCallState>,
    indirect_params: Ghost<IndirectDrawParams>,
    buffer: Ghost<BufferState>,
)
    requires
        is_recording(&*old(cb)),
        runtime_cb_wf(&*old(cb)),
        old(cb).in_render_pass@ == true,
        old(cb).recording_thread@ == thread@,
        pipeline@.alive,
        rp@.alive,
        draw_indirect_valid(old(cb).recording_state@, pipeline@, rp@, indirect_params@, buffer@),
    ensures
        is_recording(cb),
        cb.barrier_log@ == old(cb).barrier_log@,
        cb.recording_state@ == old(cb).recording_state@,
        cb.in_render_pass@ == old(cb).in_render_pass@,
        cb.recording_thread@ == old(cb).recording_thread@,
        cb.cb_id@ == old(cb).cb_id@,
        runtime_cb_wf(cb),
{
    crate::ffi::ffi_cmd_draw_indirect(ctx, cb.handle, buffer_handle, offset, draw_count, stride);
}

/// Exec: record an indirect indexed draw command.
/// Caller must prove: pipeline bound, in render pass, indirect buffer sufficient.
pub fn cmd_draw_indexed_indirect_exec(
    ctx: &VulkanContext,
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
    buffer_handle: u64,
    offset: u64,
    draw_count: u32,
    stride: u32,
    pipeline: Ghost<GraphicsPipelineState>,
    rp: Ghost<RenderPassState>,
    draw_state: Ghost<DrawCallState>,
    indirect_params: Ghost<IndirectDrawParams>,
    buffer: Ghost<BufferState>,
)
    requires
        is_recording(&*old(cb)),
        runtime_cb_wf(&*old(cb)),
        old(cb).in_render_pass@ == true,
        old(cb).recording_thread@ == thread@,
        pipeline@.alive,
        rp@.alive,
        draw_indexed_indirect_valid(old(cb).recording_state@, pipeline@, rp@, indirect_params@, buffer@),
    ensures
        is_recording(cb),
        cb.barrier_log@ == old(cb).barrier_log@,
        cb.recording_state@ == old(cb).recording_state@,
        cb.in_render_pass@ == old(cb).in_render_pass@,
        cb.recording_thread@ == old(cb).recording_thread@,
        cb.cb_id@ == old(cb).cb_id@,
        runtime_cb_wf(cb),
{
    crate::ffi::ffi_cmd_draw_indexed_indirect(ctx, cb.handle, buffer_handle, offset, draw_count, stride);
}

/// Exec: record an indirect dispatch command.
/// Caller must prove: compute pipeline bound, not in render pass, buffer sufficient.
pub fn cmd_dispatch_indirect_exec(
    ctx: &VulkanContext,
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
    buffer_handle: u64,
    buffer_offset: u64,
    pipeline: Ghost<ComputePipelineState>,
    buffer_id: Ghost<nat>,
    offset: Ghost<nat>,
    buffer: Ghost<BufferState>,
)
    requires
        is_recording(&*old(cb)),
        runtime_cb_wf(&*old(cb)),
        old(cb).in_render_pass@ == false,
        old(cb).recording_thread@ == thread@,
        pipeline@.alive,
        dispatch_indirect_valid(old(cb).recording_state@, pipeline@, buffer_id@, offset@, buffer@),
    ensures
        is_recording(cb),
        cb.barrier_log@ == old(cb).barrier_log@,
        cb.recording_state@ == old(cb).recording_state@,
        cb.in_render_pass@ == old(cb).in_render_pass@,
        cb.recording_thread@ == old(cb).recording_thread@,
        cb.cb_id@ == old(cb).cb_id@,
        runtime_cb_wf(cb),
{
    crate::ffi::ffi_cmd_dispatch_indirect(ctx, cb.handle, buffer_handle, buffer_offset);
}

/// Exec: begin dynamic rendering (VK_KHR_dynamic_rendering).
/// Sets the in_render_pass flag. Caller must prove rendering info is well-formed.
pub fn cmd_begin_dynamic_rendering_exec(
    ctx: &VulkanContext,
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
    width: u32,
    height: u32,
    layer_count: u32,
    info: Ghost<DynamicRenderingInfo>,
)
    requires
        is_recording(&*old(cb)),
        runtime_cb_wf(&*old(cb)),
        old(cb).in_render_pass@ == false,
        old(cb).recording_thread@ == thread@,
        dynamic_rendering_well_formed(info@),
    ensures
        is_recording(cb),
        cb.in_render_pass@ == true,
        cb.barrier_log@ == old(cb).barrier_log@,
        cb.recording_state@ == old(cb).recording_state@,
        cb.recording_thread@ == old(cb).recording_thread@,
        cb.cb_id@ == old(cb).cb_id@,
{
    crate::ffi::ffi_cmd_begin_rendering(ctx, cb.handle, width, height, layer_count);
    cb.in_render_pass = Ghost(true);
}

/// Exec: end dynamic rendering (VK_KHR_dynamic_rendering).
/// Clears the in_render_pass flag.
pub fn cmd_end_dynamic_rendering_exec(
    ctx: &VulkanContext,
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
)
    requires
        is_recording(&*old(cb)),
        old(cb).in_render_pass@ == true,
        old(cb).recording_thread@ == thread@,
    ensures
        is_recording(cb),
        cb.in_render_pass@ == false,
        cb.barrier_log@ == old(cb).barrier_log@,
        cb.recording_state@ == old(cb).recording_state@,
        cb.recording_thread@ == old(cb).recording_thread@,
        cb.cb_id@ == old(cb).cb_id@,
{
    crate::ffi::ffi_cmd_end_rendering(ctx, cb.handle);
    cb.in_render_pass = Ghost(false);
}

/// Whether any uncompleted submission references this command buffer.
pub open spec fn cb_has_pending_work(pending: Seq<SubmissionRecord>, cb_id: nat) -> bool {
    exists|i: int| 0 <= i < pending.len()
        && !pending[i].completed
        && pending[i].command_buffers.contains(cb_id)
}

/// Whether no uncompleted submission references this command buffer.
pub open spec fn cb_no_pending_work(pending: Seq<SubmissionRecord>, cb_id: nat) -> bool {
    forall|i: int| #![trigger pending[i]]
        0 <= i < pending.len()
        ==> pending[i].completed
            || !pending[i].command_buffers.contains(cb_id)
}

/// Exec: mark a command buffer as Pending after submission.
/// Called by the user after submit_exec succeeds.
/// Caller must prove access to the CB (typically via pool ownership after submit).
pub fn mark_pending_exec(
    cb: &mut RuntimeCommandBuffer,
    dev: &RuntimeDevice,
    thread: Ghost<ThreadId>,
    pool: Ghost<PoolOwnership>,
    reg: Ghost<TokenRegistry>,
)
    requires
        is_executable(&*old(cb)),
        can_access_child(pool@, old(cb).cb_id@, thread@, reg@),
        cb_has_pending_work(dev@.pending_submissions, old(cb).cb_id@),
    ensures
        is_pending(cb),
        cb.barrier_log@ == old(cb).barrier_log@,
        cb.recording_state@ == old(cb).recording_state@,
        cb.in_render_pass@ == old(cb).in_render_pass@,
        cb.recording_thread@ == old(cb).recording_thread@,
        cb.cb_id@ == old(cb).cb_id@,
{
    cb.status = Ghost(CommandBufferStatus::Pending);
}

/// Exec: mark a command buffer as Executable after GPU execution completes.
/// Called after a fence wait or queue_wait_idle proves the CB is no longer in-flight.
/// Caller must prove access to the CB (typically re-acquired after GPU completion).
pub fn complete_execution_exec(
    cb: &mut RuntimeCommandBuffer,
    dev: &RuntimeDevice,
    thread: Ghost<ThreadId>,
    pool: Ghost<PoolOwnership>,
    reg: Ghost<TokenRegistry>,
)
    requires
        is_pending(&*old(cb)),
        can_access_child(pool@, old(cb).cb_id@, thread@, reg@),
        cb_no_pending_work(dev@.pending_submissions, old(cb).cb_id@),
    ensures
        is_executable(cb),
        cb.barrier_log@ == old(cb).barrier_log@,
        cb.recording_state@ == old(cb).recording_state@,
        cb.in_render_pass@ == old(cb).in_render_pass@,
        cb.recording_thread@ == old(cb).recording_thread@,
        cb.cb_id@ == old(cb).cb_id@,
{
    cb.status = Ghost(CommandBufferStatus::Executable);
}

/// Exec: reset a command buffer back to Initial state.
/// In Vulkan, reset is allowed from Recording, Executable, or Invalid.
/// We support resetting from Executable (the most common case).
pub fn cmd_reset_exec(
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
    pool: Ghost<PoolOwnership>,
    reg: Ghost<TokenRegistry>,
)
    requires
        is_executable(&*old(cb)) || is_initial(&*old(cb)),
        can_access_child(pool@, old(cb).cb_id@, thread@, reg@),
    ensures
        is_initial(cb),
        cb.barrier_log@ == Seq::<BarrierEntry>::empty(),
        cb.in_render_pass@ == false,
        cb.recording_state@ == initial_recording_state(),
        cb.cb_id@ == old(cb).cb_id@,
        runtime_cb_wf(cb),
{
    cb.status = Ghost(CommandBufferStatus::Initial);
    cb.barrier_log = Ghost(Seq::empty());
    cb.in_render_pass = Ghost(false);
    cb.recording_state = Ghost(initial_recording_state());
}

// ── Extended Specs & Proofs ──────────────────────────────────────────

/// Command buffer is in initial state.
pub open spec fn is_initial(cb: &RuntimeCommandBuffer) -> bool {
    match cb.status@ {
        CommandBufferStatus::Initial => true,
        _ => false,
    }
}

/// Number of barriers recorded so far.
pub open spec fn barrier_count(cb: &RuntimeCommandBuffer) -> nat {
    cb.barrier_log@.len()
}

/// Command buffer has no recorded barriers.
pub open spec fn has_no_barriers(cb: &RuntimeCommandBuffer) -> bool {
    cb.barrier_log@.len() == 0
}

/// Proof: begin recording from initial produces recording state.
pub proof fn lemma_begin_produces_recording(cb: &RuntimeCommandBuffer, thread: ThreadId)
    requires is_initial(cb),
    ensures ({
        let new_cb = RuntimeCommandBuffer {
            handle: cb.handle,
            cb_id: cb.cb_id,
            status: Ghost(CommandBufferStatus::Recording),
            barrier_log: Ghost(Seq::empty()),
            in_render_pass: Ghost(false),
            recording_state: Ghost(initial_recording_state()),
            recording_thread: Ghost(thread),
        };
        is_recording(&new_cb)
        && runtime_cb_wf(&new_cb)
        && new_cb.recording_thread@ == thread
    }),
{
}

/// Proof: end recording from recording produces executable.
pub proof fn lemma_end_produces_executable(cb: &RuntimeCommandBuffer)
    requires
        is_recording(cb),
        runtime_cb_wf(cb),
        cb.in_render_pass@ == false,
    ensures ({
        let new_cb = RuntimeCommandBuffer {
            handle: cb.handle,
            cb_id: cb.cb_id,
            status: Ghost(CommandBufferStatus::Executable),
            barrier_log: cb.barrier_log,
            in_render_pass: cb.in_render_pass,
            recording_state: cb.recording_state,
            recording_thread: cb.recording_thread,
        };
        is_executable(&new_cb)
        && runtime_cb_wf(&new_cb)
        && new_cb.recording_thread@ == cb.recording_thread@
    }),
{
}

/// Proof: recording a barrier increments the count by 1.
pub proof fn lemma_barrier_increments_count(
    cb: &RuntimeCommandBuffer,
    entry: Ghost<BarrierEntry>,
)
    requires is_recording(cb),
    ensures cb.barrier_log@.push(entry@).len() == cb.barrier_log@.len() + 1,
{
}

/// Proof: a fresh recording has no barriers.
pub proof fn lemma_fresh_recording_no_barriers()
    ensures Seq::<BarrierEntry>::empty().len() == 0,
{
}

/// Proof: initial is not recording.
pub proof fn lemma_initial_not_recording(cb: &RuntimeCommandBuffer)
    requires is_initial(cb),
    ensures !is_recording(cb),
{
}

/// Proof: initial is not executable.
pub proof fn lemma_initial_not_executable(cb: &RuntimeCommandBuffer)
    requires is_initial(cb),
    ensures !is_executable(cb),
{
}

/// Proof: recording is not executable.
pub proof fn lemma_recording_not_executable(cb: &RuntimeCommandBuffer)
    requires is_recording(cb),
    ensures !is_executable(cb),
{
}

/// Proof: executable is not recording.
pub proof fn lemma_executable_not_recording(cb: &RuntimeCommandBuffer)
    requires is_executable(cb),
    ensures !is_recording(cb),
{
}

/// Proof: pending is not recording, not executable, and not initial.
pub proof fn lemma_pending_exclusive(cb: &RuntimeCommandBuffer)
    requires is_pending(cb),
    ensures !is_recording(cb) && !is_executable(cb) && !is_initial(cb),
{
}

/// Proof: the full lifecycle cycle: Initial → Recording → Executable → Pending → Executable.
pub proof fn lemma_full_lifecycle()
    ensures ({
        let cb0 = RuntimeCommandBuffer {
            handle: 0,
            cb_id: Ghost(0nat),
            status: Ghost(CommandBufferStatus::Initial),
            barrier_log: Ghost(Seq::empty()),
            in_render_pass: Ghost(false),
            recording_state: Ghost(initial_recording_state()),
            recording_thread: Ghost(0nat),
        };
        is_initial(&cb0) && !is_pending(&cb0)
    }),
{
}

} // verus!
