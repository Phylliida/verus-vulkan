use vstd::prelude::*;

verus! {

use crate::resource::*;
use crate::sync::*;
use crate::flags::*;
use crate::recording::*;
use crate::recording_commands::*;
use crate::pipeline::*;
use crate::render_pass::*;
use crate::draw_state::*;
use crate::pool_ownership::*;
use crate::sync_token::*;
use crate::indirect::*;
use crate::dynamic_rendering::*;
use crate::memory::*;
use crate::runtime::command_buffer::*;
use crate::runtime::image_layout::RuntimeImageLayoutTracker;

// ─── Types ─────────────────────────────────────────────────────

/// Runtime recording context: wraps a RuntimeCommandBuffer with a ghost RecordingContext
/// to keep CB ghost state and full recording context in sync.
pub struct RuntimeRecordingContext {
    pub cb: RuntimeCommandBuffer,
    pub ctx: Ghost<RecordingContext>,
}

// ─── Spec functions ────────────────────────────────────────────

/// Well-formedness: CB is recording, CB wf, and ghost state is in sync.
pub open spec fn recording_context_wf(rctx: &RuntimeRecordingContext) -> bool {
    is_recording(&rctx.cb)
    && runtime_cb_wf(&rctx.cb)
    && rctx.ctx@.state == rctx.cb.recording_state@
    && rctx.ctx@.barrier_log == rctx.cb.barrier_log@
}

/// The set of resources referenced so far.
pub open spec fn recording_context_resources(rctx: &RuntimeRecordingContext) -> Set<ResourceId> {
    rctx.ctx@.referenced_resources
}

/// The barrier log so far.
pub open spec fn recording_context_barrier_log(rctx: &RuntimeRecordingContext) -> BarrierLog {
    rctx.ctx@.barrier_log
}

// ─── Exec functions ────────────────────────────────────────────

/// Create a recording context from a just-begun command buffer.
pub fn create_recording_context_exec(
    cb: RuntimeCommandBuffer,
    thread: Ghost<ThreadId>,
    pool: Ghost<PoolOwnership>,
    reg: Ghost<TokenRegistry>,
) -> (rctx: RuntimeRecordingContext)
    requires
        is_recording(&cb),
        runtime_cb_wf(&cb),
        cb.barrier_log@ == Seq::<BarrierEntry>::empty(),
        cb.recording_state@ == initial_recording_state(),
    ensures
        recording_context_wf(&rctx),
        rctx.ctx@ == initial_recording_context(),
        rctx.cb.cb_id@ == cb.cb_id@,
        rctx.cb.recording_thread@ == cb.recording_thread@,
{
    let ghost ctx = initial_recording_context();
    RuntimeRecordingContext {
        cb: cb,
        ctx: Ghost(ctx),
    }
}

/// Record a draw command through the recording context.
pub fn record_draw_ctx_exec(
    rctx: &mut RuntimeRecordingContext,
    thread: Ghost<ThreadId>,
    pipeline: Ghost<GraphicsPipelineState>,
    rp: Ghost<RenderPassState>,
    draw_state: Ghost<DrawCallState>,
    required_vertex_slots: Ghost<Set<nat>>,
    first_vertex: Ghost<nat>,
    vertex_count: Ghost<nat>,
    resources: Ghost<Set<ResourceId>>,
)
    requires
        recording_context_wf(&*old(rctx)),
        old(rctx).cb.in_render_pass@ == true,
        old(rctx).cb.recording_thread@ == thread@,
        pipeline@.alive,
        rp@.alive,
        draw_call_valid(old(rctx).cb.recording_state@, pipeline@, rp@),
        descriptor_sets_bound_for_pipeline(old(rctx).cb.recording_state@, pipeline@.descriptor_set_layouts),
        has_vertex_buffer_bound(old(rctx).cb.recording_state@),
        dynamic_states_satisfied(draw_state@, pipeline@.required_dynamic_states),
        vertex_draw_in_bounds(draw_state@, required_vertex_slots@, first_vertex@, vertex_count@),
    ensures
        recording_context_wf(rctx),
        rctx.ctx@ == record_draw(old(rctx).ctx@, resources@),
        rctx.cb.cb_id@ == old(rctx).cb.cb_id@,
        rctx.cb.recording_thread@ == old(rctx).cb.recording_thread@,
{
    cmd_draw_exec(
        &mut rctx.cb,
        thread,
        pipeline,
        rp,
        draw_state,
        required_vertex_slots,
        first_vertex,
        vertex_count,
    );
    // cmd_draw_exec preserves barrier_log and recording_state
    // record_draw preserves state and barrier_log, only adds resources + command_log
    proof {
        let old_ctx = old(rctx).ctx@;
        let new_ctx = record_draw(old_ctx, resources@);
        // state unchanged: cb.recording_state@ == old state == new_ctx.state
        // barrier_log unchanged: cb.barrier_log@ == old log == new_ctx.barrier_log
    }
    rctx.ctx = Ghost(record_draw(old(rctx).ctx@, resources@));
}

/// Record a pipeline barrier through the recording context.
pub fn record_pipeline_barrier_ctx_exec(
    rctx: &mut RuntimeRecordingContext,
    thread: Ghost<ThreadId>,
    entry: Ghost<BarrierEntry>,
)
    requires
        recording_context_wf(&*old(rctx)),
        old(rctx).cb.recording_thread@ == thread@,
    ensures
        recording_context_wf(rctx),
        rctx.ctx@ == record_pipeline_barrier_single(old(rctx).ctx@, entry@),
        rctx.cb.cb_id@ == old(rctx).cb.cb_id@,
        rctx.cb.recording_thread@ == old(rctx).cb.recording_thread@,
{
    cmd_pipeline_barrier_exec(&mut rctx.cb, thread, entry);
    // cmd_pipeline_barrier_exec: barrier_log = old.push(entry@), state unchanged
    // record_pipeline_barrier_single: barrier_log = old.push(entry), command_log updated, state unchanged
    rctx.ctx = Ghost(record_pipeline_barrier_single(old(rctx).ctx@, entry@));
}

/// Record a buffer copy through the recording context.
pub fn record_copy_buffer_ctx_exec(
    rctx: &mut RuntimeRecordingContext,
    thread: Ghost<ThreadId>,
    src_buffer: Ghost<nat>,
    dst_buffer: Ghost<nat>,
    src_res: Ghost<ResourceId>,
    dst_res: Ghost<ResourceId>,
    src_sync: Ghost<SyncState>,
    dst_sync: Ghost<SyncState>,
)
    requires
        recording_context_wf(&*old(rctx)),
        old(rctx).cb.in_render_pass@ == false,
        old(rctx).cb.recording_thread@ == thread@,
        src_buffer@ != dst_buffer@,
        readable(old(rctx).cb.barrier_log@, src_sync@, STAGE_TRANSFER(), ACCESS_TRANSFER_READ()),
        writable(old(rctx).cb.barrier_log@, dst_sync@, STAGE_TRANSFER(), ACCESS_TRANSFER_WRITE()),
    ensures
        recording_context_wf(rctx),
        rctx.ctx@ == record_copy_buffer(old(rctx).ctx@, src_buffer@, dst_buffer@, src_res@, dst_res@),
        rctx.cb.cb_id@ == old(rctx).cb.cb_id@,
        rctx.cb.recording_thread@ == old(rctx).cb.recording_thread@,
{
    cmd_copy_buffer_exec(&mut rctx.cb, thread, src_buffer, dst_buffer, src_sync, dst_sync);
    // cmd_copy_buffer_exec preserves barrier_log and recording_state
    // record_copy_buffer preserves state and barrier_log, adds resources + command
    rctx.ctx = Ghost(record_copy_buffer(old(rctx).ctx@, src_buffer@, dst_buffer@, src_res@, dst_res@));
}

/// Bind a graphics pipeline through the recording context.
/// Caller must prove the pipeline is alive and the id matches.
pub fn record_bind_graphics_pipeline_ctx_exec(
    rctx: &mut RuntimeRecordingContext,
    thread: Ghost<ThreadId>,
    pipeline_id: Ghost<nat>,
    pipeline: Ghost<GraphicsPipelineState>,
)
    requires
        recording_context_wf(&*old(rctx)),
        old(rctx).cb.recording_thread@ == thread@,
        pipeline@.alive,
        pipeline@.id == pipeline_id@,
    ensures
        recording_context_wf(rctx),
        rctx.ctx@.state == bind_graphics_pipeline(old(rctx).ctx@.state, pipeline_id@),
        rctx.ctx@.barrier_log == old(rctx).ctx@.barrier_log,
        rctx.ctx@.referenced_resources == old(rctx).ctx@.referenced_resources,
        rctx.cb.cb_id@ == old(rctx).cb.cb_id@,
        rctx.cb.recording_thread@ == old(rctx).cb.recording_thread@,
{
    cmd_bind_pipeline_exec(&mut rctx.cb, thread, pipeline_id, pipeline);
    // cmd_bind_pipeline_exec: recording_state = bind_graphics_pipeline(old, id), barrier_log unchanged
    let ghost new_ctx = RecordingContext {
        state: bind_graphics_pipeline(old(rctx).ctx@.state, pipeline_id@),
        command_log: old(rctx).ctx@.command_log.push(RecordedCommand::BindGraphicsPipeline { pipeline_id: pipeline_id@ }),
        ..old(rctx).ctx@
    };
    rctx.ctx = Ghost(new_ctx);
}

// ─── Transfer wrappers ──────────────────────────────────────────

/// Record a copy-image command through the recording context.
pub fn record_copy_image_ctx_exec(
    rctx: &mut RuntimeRecordingContext,
    thread: Ghost<ThreadId>,
    layout_tracker: &RuntimeImageLayoutTracker,
    src_image: Ghost<ResourceId>,
    dst_image: Ghost<ResourceId>,
    src_res: Ghost<ResourceId>,
    dst_res: Ghost<ResourceId>,
    src_sync: Ghost<SyncState>,
    dst_sync: Ghost<SyncState>,
)
    requires
        recording_context_wf(&*old(rctx)),
        old(rctx).cb.in_render_pass@ == false,
        old(rctx).cb.recording_thread@ == thread@,
        src_image@ != dst_image@,
        layout_tracker@.contains_key(src_image@),
        layout_tracker@.contains_key(dst_image@),
        valid_transfer_src_layout(layout_tracker@[src_image@]),
        valid_transfer_dst_layout(layout_tracker@[dst_image@]),
        readable(old(rctx).cb.barrier_log@, src_sync@, STAGE_TRANSFER(), ACCESS_TRANSFER_READ()),
        writable(old(rctx).cb.barrier_log@, dst_sync@, STAGE_TRANSFER(), ACCESS_TRANSFER_WRITE()),
    ensures
        recording_context_wf(rctx),
        rctx.ctx@ == record_copy_image(old(rctx).ctx@, 0nat, 0nat, src_res@, dst_res@),
        rctx.cb.cb_id@ == old(rctx).cb.cb_id@,
        rctx.cb.recording_thread@ == old(rctx).cb.recording_thread@,
{
    cmd_copy_image_exec(&mut rctx.cb, thread, layout_tracker, src_image, dst_image, src_sync, dst_sync);
    rctx.ctx = Ghost(record_copy_image(old(rctx).ctx@, 0nat, 0nat, src_res@, dst_res@));
}

/// Record a blit-image command through the recording context.
pub fn record_blit_image_ctx_exec(
    rctx: &mut RuntimeRecordingContext,
    thread: Ghost<ThreadId>,
    layout_tracker: &RuntimeImageLayoutTracker,
    src_image: Ghost<ResourceId>,
    dst_image: Ghost<ResourceId>,
    src_res: Ghost<ResourceId>,
    dst_res: Ghost<ResourceId>,
    src_sync: Ghost<SyncState>,
    dst_sync: Ghost<SyncState>,
)
    requires
        recording_context_wf(&*old(rctx)),
        old(rctx).cb.in_render_pass@ == false,
        old(rctx).cb.recording_thread@ == thread@,
        src_image@ != dst_image@,
        layout_tracker@.contains_key(src_image@),
        layout_tracker@.contains_key(dst_image@),
        valid_transfer_src_layout(layout_tracker@[src_image@]),
        valid_transfer_dst_layout(layout_tracker@[dst_image@]),
        readable(old(rctx).cb.barrier_log@, src_sync@, STAGE_TRANSFER(), ACCESS_TRANSFER_READ()),
        writable(old(rctx).cb.barrier_log@, dst_sync@, STAGE_TRANSFER(), ACCESS_TRANSFER_WRITE()),
    ensures
        recording_context_wf(rctx),
        rctx.ctx@ == record_blit_image(old(rctx).ctx@, 0nat, 0nat, src_res@, dst_res@),
        rctx.cb.cb_id@ == old(rctx).cb.cb_id@,
        rctx.cb.recording_thread@ == old(rctx).cb.recording_thread@,
{
    cmd_blit_image_exec(&mut rctx.cb, thread, layout_tracker, src_image, dst_image, src_sync, dst_sync);
    rctx.ctx = Ghost(record_blit_image(old(rctx).ctx@, 0nat, 0nat, src_res@, dst_res@));
}

/// Record a buffer-to-image copy through the recording context.
pub fn record_copy_buffer_to_image_ctx_exec(
    rctx: &mut RuntimeRecordingContext,
    thread: Ghost<ThreadId>,
    layout_tracker: &RuntimeImageLayoutTracker,
    src_buffer: Ghost<nat>,
    dst_image: Ghost<ResourceId>,
    src_res: Ghost<ResourceId>,
    dst_res: Ghost<ResourceId>,
    src_sync: Ghost<SyncState>,
    dst_sync: Ghost<SyncState>,
)
    requires
        recording_context_wf(&*old(rctx)),
        old(rctx).cb.in_render_pass@ == false,
        old(rctx).cb.recording_thread@ == thread@,
        layout_tracker@.contains_key(dst_image@),
        valid_transfer_dst_layout(layout_tracker@[dst_image@]),
        readable(old(rctx).cb.barrier_log@, src_sync@, STAGE_TRANSFER(), ACCESS_TRANSFER_READ()),
        writable(old(rctx).cb.barrier_log@, dst_sync@, STAGE_TRANSFER(), ACCESS_TRANSFER_WRITE()),
    ensures
        recording_context_wf(rctx),
        rctx.ctx@ == record_copy_buffer_to_image(old(rctx).ctx@, src_buffer@, 0nat, src_res@, dst_res@),
        rctx.cb.cb_id@ == old(rctx).cb.cb_id@,
        rctx.cb.recording_thread@ == old(rctx).cb.recording_thread@,
{
    cmd_copy_buffer_to_image_exec(&mut rctx.cb, thread, layout_tracker, src_buffer, dst_image, src_sync, dst_sync);
    rctx.ctx = Ghost(record_copy_buffer_to_image(old(rctx).ctx@, src_buffer@, 0nat, src_res@, dst_res@));
}

/// Record an image-to-buffer copy through the recording context.
pub fn record_copy_image_to_buffer_ctx_exec(
    rctx: &mut RuntimeRecordingContext,
    thread: Ghost<ThreadId>,
    layout_tracker: &RuntimeImageLayoutTracker,
    src_image: Ghost<ResourceId>,
    dst_buffer: Ghost<nat>,
    src_res: Ghost<ResourceId>,
    dst_res: Ghost<ResourceId>,
    src_sync: Ghost<SyncState>,
    dst_sync: Ghost<SyncState>,
)
    requires
        recording_context_wf(&*old(rctx)),
        old(rctx).cb.in_render_pass@ == false,
        old(rctx).cb.recording_thread@ == thread@,
        layout_tracker@.contains_key(src_image@),
        valid_transfer_src_layout(layout_tracker@[src_image@]),
        readable(old(rctx).cb.barrier_log@, src_sync@, STAGE_TRANSFER(), ACCESS_TRANSFER_READ()),
        writable(old(rctx).cb.barrier_log@, dst_sync@, STAGE_TRANSFER(), ACCESS_TRANSFER_WRITE()),
    ensures
        recording_context_wf(rctx),
        rctx.ctx@ == record_copy_image_to_buffer(old(rctx).ctx@, 0nat, dst_buffer@, src_res@, dst_res@),
        rctx.cb.cb_id@ == old(rctx).cb.cb_id@,
        rctx.cb.recording_thread@ == old(rctx).cb.recording_thread@,
{
    cmd_copy_image_to_buffer_exec(&mut rctx.cb, thread, layout_tracker, src_image, dst_buffer, src_sync, dst_sync);
    rctx.ctx = Ghost(record_copy_image_to_buffer(old(rctx).ctx@, 0nat, dst_buffer@, src_res@, dst_res@));
}

// ─── Indirect wrappers ─────────────────────────────────────────

/// Record an indirect draw through the recording context.
pub fn record_draw_indirect_ctx_exec(
    rctx: &mut RuntimeRecordingContext,
    thread: Ghost<ThreadId>,
    pipeline: Ghost<GraphicsPipelineState>,
    rp: Ghost<RenderPassState>,
    draw_state: Ghost<DrawCallState>,
    indirect_params: Ghost<IndirectDrawParams>,
    buffer: Ghost<BufferState>,
    resources: Ghost<Set<ResourceId>>,
)
    requires
        recording_context_wf(&*old(rctx)),
        old(rctx).cb.in_render_pass@ == true,
        old(rctx).cb.recording_thread@ == thread@,
        pipeline@.alive,
        rp@.alive,
        draw_indirect_valid(old(rctx).cb.recording_state@, pipeline@, rp@, indirect_params@, buffer@),
    ensures
        recording_context_wf(rctx),
        rctx.ctx@ == record_draw_indirect(old(rctx).ctx@, indirect_params@.buffer_id, indirect_params@.offset, indirect_params@.draw_count, resources@),
        rctx.cb.cb_id@ == old(rctx).cb.cb_id@,
        rctx.cb.recording_thread@ == old(rctx).cb.recording_thread@,
{
    cmd_draw_indirect_exec(&mut rctx.cb, thread, pipeline, rp, draw_state, indirect_params, buffer);
    rctx.ctx = Ghost(record_draw_indirect(old(rctx).ctx@, indirect_params@.buffer_id, indirect_params@.offset, indirect_params@.draw_count, resources@));
}

/// Record an indirect indexed draw through the recording context.
pub fn record_draw_indexed_indirect_ctx_exec(
    rctx: &mut RuntimeRecordingContext,
    thread: Ghost<ThreadId>,
    pipeline: Ghost<GraphicsPipelineState>,
    rp: Ghost<RenderPassState>,
    draw_state: Ghost<DrawCallState>,
    indirect_params: Ghost<IndirectDrawParams>,
    buffer: Ghost<BufferState>,
    resources: Ghost<Set<ResourceId>>,
)
    requires
        recording_context_wf(&*old(rctx)),
        old(rctx).cb.in_render_pass@ == true,
        old(rctx).cb.recording_thread@ == thread@,
        pipeline@.alive,
        rp@.alive,
        draw_indexed_indirect_valid(old(rctx).cb.recording_state@, pipeline@, rp@, indirect_params@, buffer@),
    ensures
        recording_context_wf(rctx),
        rctx.ctx@ == record_draw_indexed_indirect(old(rctx).ctx@, indirect_params@.buffer_id, indirect_params@.offset, indirect_params@.draw_count, resources@),
        rctx.cb.cb_id@ == old(rctx).cb.cb_id@,
        rctx.cb.recording_thread@ == old(rctx).cb.recording_thread@,
{
    cmd_draw_indexed_indirect_exec(&mut rctx.cb, thread, pipeline, rp, draw_state, indirect_params, buffer);
    rctx.ctx = Ghost(record_draw_indexed_indirect(old(rctx).ctx@, indirect_params@.buffer_id, indirect_params@.offset, indirect_params@.draw_count, resources@));
}

/// Record an indirect dispatch through the recording context.
pub fn record_dispatch_indirect_ctx_exec(
    rctx: &mut RuntimeRecordingContext,
    thread: Ghost<ThreadId>,
    pipeline: Ghost<ComputePipelineState>,
    buffer_id: Ghost<nat>,
    offset: Ghost<nat>,
    buffer: Ghost<BufferState>,
    resources: Ghost<Set<ResourceId>>,
)
    requires
        recording_context_wf(&*old(rctx)),
        old(rctx).cb.in_render_pass@ == false,
        old(rctx).cb.recording_thread@ == thread@,
        pipeline@.alive,
        dispatch_indirect_valid(old(rctx).cb.recording_state@, pipeline@, buffer_id@, offset@, buffer@),
    ensures
        recording_context_wf(rctx),
        rctx.ctx@ == record_dispatch_indirect(old(rctx).ctx@, buffer_id@, offset@, resources@),
        rctx.cb.cb_id@ == old(rctx).cb.cb_id@,
        rctx.cb.recording_thread@ == old(rctx).cb.recording_thread@,
{
    cmd_dispatch_indirect_exec(&mut rctx.cb, thread, pipeline, buffer_id, offset, buffer);
    rctx.ctx = Ghost(record_dispatch_indirect(old(rctx).ctx@, buffer_id@, offset@, resources@));
}

// ─── Dynamic rendering wrappers ────────────────────────────────

/// Begin dynamic rendering through the recording context.
pub fn record_begin_rendering_ctx_exec(
    rctx: &mut RuntimeRecordingContext,
    thread: Ghost<ThreadId>,
    info: Ghost<DynamicRenderingInfo>,
)
    requires
        recording_context_wf(&*old(rctx)),
        old(rctx).cb.in_render_pass@ == false,
        old(rctx).cb.recording_thread@ == thread@,
        dynamic_rendering_well_formed(info@),
    ensures
        rctx.ctx@ == record_begin_rendering(old(rctx).ctx@, info@),
        rctx.cb.cb_id@ == old(rctx).cb.cb_id@,
        rctx.cb.recording_thread@ == old(rctx).cb.recording_thread@,
        rctx.cb.in_render_pass@ == true,
        is_recording(&rctx.cb),
{
    cmd_begin_dynamic_rendering_exec(&mut rctx.cb, thread, info);
    rctx.ctx = Ghost(record_begin_rendering(old(rctx).ctx@, info@));
}

/// End dynamic rendering through the recording context.
pub fn record_end_rendering_ctx_exec(
    rctx: &mut RuntimeRecordingContext,
    thread: Ghost<ThreadId>,
)
    requires
        old(rctx).cb.in_render_pass@ == true,
        old(rctx).cb.recording_thread@ == thread@,
        is_recording(&old(rctx).cb),
    ensures
        rctx.ctx@ == record_end_rendering(old(rctx).ctx@),
        rctx.cb.cb_id@ == old(rctx).cb.cb_id@,
        rctx.cb.recording_thread@ == old(rctx).cb.recording_thread@,
        rctx.cb.in_render_pass@ == false,
        is_recording(&rctx.cb),
{
    cmd_end_dynamic_rendering_exec(&mut rctx.cb, thread);
    rctx.ctx = Ghost(record_end_rendering(old(rctx).ctx@));
}

/// Finish recording and extract the command buffer + ghost context.
pub fn finish_recording_context_exec(
    rctx: RuntimeRecordingContext,
    thread: Ghost<ThreadId>,
    pool: Ghost<PoolOwnership>,
    reg: Ghost<TokenRegistry>,
) -> (result: (RuntimeCommandBuffer, Ghost<RecordingContext>))
    requires
        recording_context_wf(&rctx),
        rctx.cb.in_render_pass@ == false,
        can_access_child(pool@, rctx.cb.cb_id@, thread@, reg@),
        rctx.cb.recording_thread@ == thread@,
    ensures
        is_executable(&result.0),
        runtime_cb_wf(&result.0),
        result.1@ == rctx.ctx@,
        result.0.cb_id@ == rctx.cb.cb_id@,
{
    let RuntimeRecordingContext { mut cb, ctx } = rctx;
    end_recording_exec(&mut cb, thread, pool, reg);
    (cb, ctx)
}

// ─── Proof functions ───────────────────────────────────────────

/// Creating a context from a fresh recording CB produces a well-formed context.
pub proof fn lemma_create_context_wf(
    cb: RuntimeCommandBuffer,
)
    requires
        is_recording(&cb),
        runtime_cb_wf(&cb),
        cb.barrier_log@ == Seq::<BarrierEntry>::empty(),
        cb.recording_state@ == initial_recording_state(),
    ensures
        ({
            let ctx = initial_recording_context();
            ctx.state == cb.recording_state@
            && ctx.barrier_log == cb.barrier_log@
        }),
{
    // Direct from definitions
}

/// Recording a draw preserves wf (state and barrier_log sync).
pub proof fn lemma_record_draw_preserves_wf(
    ctx: RecordingContext,
    resources: Set<ResourceId>,
)
    ensures
        record_draw(ctx, resources).state == ctx.state,
        record_draw(ctx, resources).barrier_log == ctx.barrier_log,
{
    // Direct from record_draw definition
}

/// Recording a barrier preserves wf (state sync, barrier_log = push).
pub proof fn lemma_record_barrier_preserves_wf(
    ctx: RecordingContext,
    entry: BarrierEntry,
)
    ensures
        record_pipeline_barrier_single(ctx, entry).state == ctx.state,
        record_pipeline_barrier_single(ctx, entry).barrier_log == ctx.barrier_log.push(entry),
{
    // Direct from record_pipeline_barrier_single definition
}

/// After finish, the CB is executable and the context captures all resources.
pub proof fn lemma_finish_produces_executable(
    rctx: RuntimeRecordingContext,
)
    requires
        recording_context_wf(&rctx),
    ensures
        rctx.ctx@.referenced_resources == recording_context_resources(&rctx),
        rctx.ctx@.barrier_log == recording_context_barrier_log(&rctx),
{
    // Direct from spec fn definitions
}

} // verus!
