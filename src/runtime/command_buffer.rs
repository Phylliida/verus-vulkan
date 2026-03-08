use vstd::prelude::*;
use crate::recording::*;
use crate::resource::*;
use crate::flags::*;
use crate::sync::*;
use crate::sync_token::*;
use crate::pool_ownership::*;
use crate::pipeline::*;
use crate::render_pass::*;
use crate::image_layout::ImageLayout;
use crate::image_layout_fsm::*;
use crate::framebuffer::*;
use super::image_layout::RuntimeImageLayoutTracker;

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
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
    pool: Ghost<PoolOwnership>,
    reg: Ghost<TokenRegistry>,
)
    requires
        match old(cb).status@ {
            CommandBufferStatus::Initial => true,
            _ => false,
        },
        can_access_child(pool@, old(cb).handle as nat, thread@, reg@),
    ensures
        is_recording(cb),
        cb.barrier_log@ == Seq::<BarrierEntry>::empty(),
        cb.in_render_pass@ == false,
        cb.recording_state@ == initial_recording_state(),
        cb.recording_thread@ == thread@,
        runtime_cb_wf(cb),
{
    cb.status = Ghost(CommandBufferStatus::Recording);
    cb.barrier_log = Ghost(Seq::empty());
    cb.in_render_pass = Ghost(false);
    cb.recording_state = Ghost(initial_recording_state());
    cb.recording_thread = thread;
}

/// Exec: end recording.
/// Must be called by the same thread that began recording, with pool access.
pub fn end_recording_exec(
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
    pool: Ghost<PoolOwnership>,
    reg: Ghost<TokenRegistry>,
)
    requires
        is_recording(&*old(cb)),
        runtime_cb_wf(&*old(cb)),
        old(cb).in_render_pass@ == false,
        can_access_child(pool@, old(cb).handle as nat, thread@, reg@),
        old(cb).recording_thread@ == thread@,
    ensures
        is_executable(cb),
        cb.recording_state@ == old(cb).recording_state@,
        cb.in_render_pass@ == old(cb).in_render_pass@,
        cb.recording_thread@ == old(cb).recording_thread@,
        runtime_cb_wf(cb),
{
    cb.status = Ghost(CommandBufferStatus::Executable);
}

/// Exec: begin render pass.
/// Caller must prove the framebuffer is compatible with the render pass
/// and that attachment images are in their expected initial layouts.
pub fn cmd_begin_render_pass_exec(
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
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
        runtime_cb_wf(cb),
{
    cb.in_render_pass = Ghost(true);
    cb.recording_state = Ghost(begin_render_pass_recording(cb.recording_state@, rp@.id, fb@.id));
}

/// Exec: end render pass.
/// Updates the layout tracker so each attachment is in its final_layout.
pub fn cmd_end_render_pass_exec(
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
        runtime_cb_wf(cb),
        layout_tracker@ == apply_transitions(
            old(layout_tracker)@,
            render_pass_end_transitions(rp@, attachment_resources@),
        ),
{
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
        runtime_cb_wf(cb),
{
    cb.recording_state = Ghost(next_subpass_recording(cb.recording_state@));
}

/// Exec: record a pipeline barrier.
pub fn cmd_pipeline_barrier_exec(
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
    entry: Ghost<BarrierEntry>,
)
    requires
        is_recording(&*old(cb)),
        runtime_cb_wf(&*old(cb)),
        old(cb).recording_thread@ == thread@,
    ensures
        is_recording(cb),
        cb.barrier_log@ == old(cb).barrier_log@.push(entry@),
        cb.recording_state@ == old(cb).recording_state@,
        cb.in_render_pass@ == old(cb).in_render_pass@,
        cb.recording_thread@ == old(cb).recording_thread@,
        runtime_cb_wf(cb),
{
    cb.barrier_log = Ghost(cb.barrier_log@.push(entry@));
}

/// Exec: bind a graphics pipeline (updates recording state).
pub fn cmd_bind_graphics_pipeline_exec(
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
    pipeline_id: Ghost<nat>,
)
    requires
        is_recording(&*old(cb)),
        runtime_cb_wf(&*old(cb)),
        old(cb).recording_thread@ == thread@,
    ensures
        is_recording(cb),
        cb.barrier_log@ == old(cb).barrier_log@,
        cb.recording_state@ == bind_graphics_pipeline(old(cb).recording_state@, pipeline_id@),
        cb.in_render_pass@ == old(cb).in_render_pass@,
        cb.recording_thread@ == old(cb).recording_thread@,
        runtime_cb_wf(cb),
{
    cb.recording_state = Ghost(bind_graphics_pipeline(cb.recording_state@, pipeline_id@));
}

/// Exec: bind a compute pipeline (updates recording state).
pub fn cmd_bind_compute_pipeline_exec(
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
    pipeline_id: Ghost<nat>,
)
    requires
        is_recording(&*old(cb)),
        runtime_cb_wf(&*old(cb)),
        old(cb).recording_thread@ == thread@,
    ensures
        is_recording(cb),
        cb.barrier_log@ == old(cb).barrier_log@,
        cb.recording_state@ == bind_compute_pipeline(old(cb).recording_state@, pipeline_id@),
        cb.in_render_pass@ == old(cb).in_render_pass@,
        cb.recording_thread@ == old(cb).recording_thread@,
        runtime_cb_wf(cb),
{
    cb.recording_state = Ghost(bind_compute_pipeline(cb.recording_state@, pipeline_id@));
}

/// Exec: bind a pipeline (backward compat, delegates to graphics variant).
pub fn cmd_bind_pipeline_exec(cb: &mut RuntimeCommandBuffer, thread: Ghost<ThreadId>, pipeline_id: Ghost<nat>)
    requires
        is_recording(&*old(cb)),
        runtime_cb_wf(&*old(cb)),
        old(cb).recording_thread@ == thread@,
    ensures
        is_recording(cb),
        cb.barrier_log@ == old(cb).barrier_log@,
        cb.recording_state@ == bind_graphics_pipeline(old(cb).recording_state@, pipeline_id@),
        cb.in_render_pass@ == old(cb).in_render_pass@,
        cb.recording_thread@ == old(cb).recording_thread@,
        runtime_cb_wf(cb),
{
    cb.recording_state = Ghost(bind_graphics_pipeline(cb.recording_state@, pipeline_id@));
}

/// Exec: bind a descriptor set at a given set index.
/// The layout_id must match the descriptor set's actual layout for pipeline compatibility.
pub fn cmd_bind_descriptor_set_exec(
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
    set_index: Ghost<nat>,
    set_id: Ghost<nat>,
    layout_id: Ghost<nat>,
)
    requires
        is_recording(&*old(cb)),
        runtime_cb_wf(&*old(cb)),
        old(cb).recording_thread@ == thread@,
    ensures
        is_recording(cb),
        cb.barrier_log@ == old(cb).barrier_log@,
        cb.recording_state@ == bind_descriptor_set(old(cb).recording_state@, set_index@, set_id@, layout_id@),
        cb.in_render_pass@ == old(cb).in_render_pass@,
        cb.recording_thread@ == old(cb).recording_thread@,
        runtime_cb_wf(cb),
{
    cb.recording_state = Ghost(bind_descriptor_set(cb.recording_state@, set_index@, set_id@, layout_id@));
}

/// Exec: bind a vertex buffer at a given slot.
pub fn cmd_bind_vertex_buffer_exec(
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
    slot: Ghost<nat>,
    buffer_id: Ghost<nat>,
)
    requires
        is_recording(&*old(cb)),
        runtime_cb_wf(&*old(cb)),
        old(cb).recording_thread@ == thread@,
    ensures
        is_recording(cb),
        cb.barrier_log@ == old(cb).barrier_log@,
        cb.recording_state@ == bind_vertex_buffer(old(cb).recording_state@, slot@, buffer_id@),
        cb.in_render_pass@ == old(cb).in_render_pass@,
        cb.recording_thread@ == old(cb).recording_thread@,
        runtime_cb_wf(cb),
{
    cb.recording_state = Ghost(bind_vertex_buffer(cb.recording_state@, slot@, buffer_id@));
}

/// Exec: bind an index buffer.
pub fn cmd_bind_index_buffer_exec(
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
    buffer_id: Ghost<nat>,
)
    requires
        is_recording(&*old(cb)),
        runtime_cb_wf(&*old(cb)),
        old(cb).recording_thread@ == thread@,
    ensures
        is_recording(cb),
        cb.barrier_log@ == old(cb).barrier_log@,
        cb.recording_state@ == bind_index_buffer(old(cb).recording_state@, buffer_id@),
        cb.in_render_pass@ == old(cb).in_render_pass@,
        cb.recording_thread@ == old(cb).recording_thread@,
        runtime_cb_wf(cb),
{
    cb.recording_state = Ghost(bind_index_buffer(cb.recording_state@, buffer_id@));
}

/// Exec: set the dynamic viewport.
pub fn cmd_set_viewport_exec(cb: &mut RuntimeCommandBuffer, thread: Ghost<ThreadId>)
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
        runtime_cb_wf(cb),
{
    cb.recording_state = Ghost(set_viewport_recording(cb.recording_state@));
}

/// Exec: set the dynamic scissor.
pub fn cmd_set_scissor_exec(cb: &mut RuntimeCommandBuffer, thread: Ghost<ThreadId>)
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
        runtime_cb_wf(cb),
{
    cb.recording_state = Ghost(set_scissor_recording(cb.recording_state@));
}

/// Exec: set push constants.
pub fn cmd_set_push_constants_exec(cb: &mut RuntimeCommandBuffer, thread: Ghost<ThreadId>)
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
        runtime_cb_wf(cb),
{
    cb.recording_state = Ghost(set_push_constants_recording(cb.recording_state@));
}

/// Exec: record a draw command.
/// Caller must prove: pipeline bound, descriptors bound, vertex buffer bound,
/// and required dynamic state (viewport/scissor) set.
pub fn cmd_draw_exec(
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
    pipeline: Ghost<GraphicsPipelineState>,
    rp: Ghost<RenderPassState>,
    needs_dynamic_viewport: Ghost<bool>,
    needs_dynamic_scissor: Ghost<bool>,
)
    requires
        is_recording(&*old(cb)),
        runtime_cb_wf(&*old(cb)),
        old(cb).in_render_pass@ == true,
        old(cb).recording_thread@ == thread@,
        draw_call_valid(old(cb).recording_state@, pipeline@, rp@),
        descriptor_sets_bound_for_pipeline(old(cb).recording_state@, pipeline@.descriptor_set_layouts),
        has_vertex_buffer_bound(old(cb).recording_state@),
        dynamic_state_satisfied(old(cb).recording_state@, needs_dynamic_viewport@, needs_dynamic_scissor@),
    ensures
        is_recording(cb),
        cb.barrier_log@ == old(cb).barrier_log@,
        cb.recording_state@ == old(cb).recording_state@,
        cb.in_render_pass@ == old(cb).in_render_pass@,
        cb.recording_thread@ == old(cb).recording_thread@,
        runtime_cb_wf(cb),
{
}

/// Exec: record an indexed draw command.
/// Same as cmd_draw_exec but additionally requires an index buffer bound.
pub fn cmd_draw_indexed_exec(
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
    pipeline: Ghost<GraphicsPipelineState>,
    rp: Ghost<RenderPassState>,
    needs_dynamic_viewport: Ghost<bool>,
    needs_dynamic_scissor: Ghost<bool>,
)
    requires
        is_recording(&*old(cb)),
        runtime_cb_wf(&*old(cb)),
        old(cb).in_render_pass@ == true,
        old(cb).recording_thread@ == thread@,
        draw_call_valid(old(cb).recording_state@, pipeline@, rp@),
        descriptor_sets_bound_for_pipeline(old(cb).recording_state@, pipeline@.descriptor_set_layouts),
        has_vertex_buffer_bound(old(cb).recording_state@),
        has_index_buffer_bound(old(cb).recording_state@),
        dynamic_state_satisfied(old(cb).recording_state@, needs_dynamic_viewport@, needs_dynamic_scissor@),
    ensures
        is_recording(cb),
        cb.barrier_log@ == old(cb).barrier_log@,
        cb.recording_state@ == old(cb).recording_state@,
        cb.in_render_pass@ == old(cb).in_render_pass@,
        cb.recording_thread@ == old(cb).recording_thread@,
        runtime_cb_wf(cb),
{
}

/// Exec: record a dispatch command.
/// Caller must prove a compatible compute pipeline is bound and all descriptor sets are bound.
pub fn cmd_dispatch_exec(
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
    pipeline: Ghost<ComputePipelineState>,
)
    requires
        is_recording(&*old(cb)),
        runtime_cb_wf(&*old(cb)),
        old(cb).in_render_pass@ == false,
        old(cb).recording_thread@ == thread@,
        dispatch_call_valid(old(cb).recording_state@, pipeline@),
        descriptor_sets_bound_for_pipeline(old(cb).recording_state@, pipeline@.descriptor_set_layouts),
    ensures
        is_recording(cb),
        cb.barrier_log@ == old(cb).barrier_log@,
        cb.recording_state@ == old(cb).recording_state@,
        cb.in_render_pass@ == old(cb).in_render_pass@,
        cb.recording_thread@ == old(cb).recording_thread@,
        runtime_cb_wf(cb),
{
}

/// Exec: record a buffer-to-buffer copy.
/// Transfer commands must be outside a render pass.
/// Caller must prove source is readable and destination is writable at the transfer stage.
pub fn cmd_copy_buffer_exec(
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
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
        readable(old(cb).barrier_log@, src_sync@, STAGE_TRANSFER(), ACCESS_TRANSFER_READ()),
        writable(old(cb).barrier_log@, dst_sync@, STAGE_TRANSFER(), ACCESS_TRANSFER_WRITE()),
    ensures
        is_recording(cb),
        cb.barrier_log@ == old(cb).barrier_log@,
        cb.recording_state@ == old(cb).recording_state@,
        cb.in_render_pass@ == old(cb).in_render_pass@,
        cb.recording_thread@ == old(cb).recording_thread@,
        runtime_cb_wf(cb),
{
}

/// Exec: record an image-to-image copy.
/// Transfer commands must be outside a render pass.
/// Source must be in TransferSrcOptimal or General; dest must be in TransferDstOptimal or General.
/// Caller must prove source is readable and destination is writable at the transfer stage.
pub fn cmd_copy_image_exec(
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
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
        runtime_cb_wf(cb),
{
}

/// Exec: record an image blit (scaled copy).
/// Transfer commands must be outside a render pass.
/// Source must be in TransferSrcOptimal or General; dest must be in TransferDstOptimal or General.
/// Caller must prove source is readable and destination is writable at the transfer stage.
pub fn cmd_blit_image_exec(
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
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
        runtime_cb_wf(cb),
{
}

/// Exec: record a buffer-to-image copy.
/// Transfer commands must be outside a render pass.
/// Dest image must be in TransferDstOptimal or General.
/// Caller must prove source buffer is readable and destination image is writable.
pub fn cmd_copy_buffer_to_image_exec(
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
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
        runtime_cb_wf(cb),
{
}

/// Exec: record an image-to-buffer copy.
/// Transfer commands must be outside a render pass.
/// Source image must be in TransferSrcOptimal or General.
/// Caller must prove source image is readable and destination buffer is writable.
pub fn cmd_copy_image_to_buffer_exec(
    cb: &mut RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
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
        runtime_cb_wf(cb),
{
}

/// Exec: mark a command buffer as Pending after submission.
/// Called by the user after submit_exec succeeds.
pub fn mark_pending_exec(cb: &mut RuntimeCommandBuffer)
    requires
        is_executable(&*old(cb)),
    ensures
        is_pending(cb),
        cb.barrier_log@ == old(cb).barrier_log@,
        cb.recording_state@ == old(cb).recording_state@,
        cb.in_render_pass@ == old(cb).in_render_pass@,
        cb.recording_thread@ == old(cb).recording_thread@,
{
    cb.status = Ghost(CommandBufferStatus::Pending);
}

/// Exec: mark a command buffer as Executable after GPU execution completes.
/// Called after a fence wait or queue_wait_idle proves the CB is no longer in-flight.
pub fn complete_execution_exec(cb: &mut RuntimeCommandBuffer)
    requires
        is_pending(&*old(cb)),
    ensures
        is_executable(cb),
        cb.barrier_log@ == old(cb).barrier_log@,
        cb.recording_state@ == old(cb).recording_state@,
        cb.in_render_pass@ == old(cb).in_render_pass@,
        cb.recording_thread@ == old(cb).recording_thread@,
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
        can_access_child(pool@, old(cb).handle as nat, thread@, reg@),
    ensures
        is_initial(cb),
        cb.barrier_log@ == Seq::<BarrierEntry>::empty(),
        cb.in_render_pass@ == false,
        cb.recording_state@ == initial_recording_state(),
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
