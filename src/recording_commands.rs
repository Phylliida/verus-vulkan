use vstd::prelude::*;
use crate::resource::*;
use crate::recording::*;
use crate::pipeline::*;
use crate::render_pass::*;
use crate::flags::*;
use crate::sync::*;
use crate::sync_proofs::*;
use crate::stage_access::*;
use crate::dynamic_rendering::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// A recorded command in the command buffer log.
pub enum RecordedCommand {
    Draw,
    DrawIndexed,
    Dispatch { group_count_x: nat, group_count_y: nat, group_count_z: nat },
    CopyBuffer { src_buffer: nat, dst_buffer: nat },
    CopyImage { src_image: nat, dst_image: nat },
    BlitImage { src_image: nat, dst_image: nat },
    CopyBufferToImage { src_buffer: nat, dst_image: nat },
    CopyImageToBuffer { src_image: nat, dst_buffer: nat },
    DrawIndirect { buffer: nat, offset: nat, draw_count: nat },
    DrawIndexedIndirect { buffer: nat, offset: nat, draw_count: nat },
    DispatchIndirect { buffer: nat, offset: nat },
    BeginRendering { info: DynamicRenderingInfo },
    EndRendering,
    BindGraphicsPipeline { pipeline_id: nat },
    BindComputePipeline { pipeline_id: nat },
    BindDescriptorSet { set_index: nat, set_id: nat },
    BeginRenderPass { rp_id: nat, fb_id: nat },
    EndRenderPass,
    NextSubpass,
    PipelineBarrier { barriers: Seq<BarrierEntry> },
    FillBuffer { buffer: nat, offset: nat, size: nat },
    UpdateBuffer { buffer: nat, offset: nat, size: nat },
    ClearColorImage { image: nat },
    ClearDepthStencilImage { image: nat },
    ClearAttachments,
    ResolveImage { src_image: nat, dst_image: nat },
    WriteTimestamp { pool_id: nat, query: nat },
    CopyQueryPoolResults { pool_id: nat, first_query: nat, query_count: nat, dst_buffer: nat },
    WaitEvents { barriers: Seq<BarrierEntry> },
    DrawIndirectCount { buffer: nat, offset: nat, count_buffer: nat, count_offset: nat, max_draw_count: nat },
    DrawIndexedIndirectCount { buffer: nat, offset: nat, count_buffer: nat, count_offset: nat, max_draw_count: nat },
    TraceRays,
    TraceRaysIndirect { buffer: nat },
    DispatchBase { base_x: nat, base_y: nat, base_z: nat, group_x: nat, group_y: nat, group_z: nat },
    DrawMeshTasks { group_count_x: nat, group_count_y: nat, group_count_z: nat },
    DrawMeshTasksIndirect { buffer: nat, offset: nat, draw_count: nat },
    DrawMeshTasksIndirectCount { buffer: nat, offset: nat, count_buffer: nat, count_offset: nat, max_draw_count: nat },
    BeginTransformFeedback,
    EndTransformFeedback,
    PipelineBarrier2 { barriers: Seq<BarrierEntry> },
}

/// Tracks the full recording context: current state, referenced resources,
/// and the command log.
pub struct RecordingContext {
    /// Current recording state (bound pipelines, descriptor sets, render pass).
    pub state: RecordingState,
    /// Accumulated set of all resources referenced by recorded commands.
    pub referenced_resources: Set<ResourceId>,
    /// Ordered log of recorded commands.
    pub command_log: Seq<RecordedCommand>,
    /// Log of barriers inserted during recording (for sync validation).
    pub barrier_log: BarrierLog,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// An empty recording context: initial state, no resources, no commands.
pub open spec fn initial_recording_context() -> RecordingContext {
    RecordingContext {
        state: initial_recording_state(),
        referenced_resources: Set::empty(),
        command_log: Seq::empty(),
        barrier_log: Seq::empty(),
    }
}

/// A draw call is fully valid: both the recording state check and
/// descriptor set bindings are satisfied.
pub open spec fn full_draw_call_valid(
    ctx: RecordingContext,
    pipeline: GraphicsPipelineState,
    rp: RenderPassState,
) -> bool {
    draw_call_valid(ctx.state, pipeline, rp)
    && descriptor_sets_bound_for_pipeline(ctx.state, pipeline.descriptor_set_layouts)
}

/// A dispatch call is fully valid: both the recording state check and
/// descriptor set bindings are satisfied.
pub open spec fn full_dispatch_call_valid(
    ctx: RecordingContext,
    pipeline: ComputePipelineState,
) -> bool {
    dispatch_call_valid(ctx.state, pipeline)
    && descriptor_sets_bound_for_pipeline(ctx.state, pipeline.descriptor_set_layouts)
}

/// Record a draw command: append to the log and accumulate resources.
/// The recording state is unchanged.
pub open spec fn record_draw(
    ctx: RecordingContext,
    resources: Set<ResourceId>,
) -> RecordingContext {
    RecordingContext {
        state: ctx.state,
        referenced_resources: ctx.referenced_resources.union(resources),
        command_log: ctx.command_log.push(RecordedCommand::Draw),
        barrier_log: ctx.barrier_log,
    }
}

/// Record a copy-buffer command: append to the log and add both resource ids.
pub open spec fn record_copy_buffer(
    ctx: RecordingContext,
    src: nat,
    dst: nat,
    src_res: ResourceId,
    dst_res: ResourceId,
) -> RecordingContext {
    RecordingContext {
        state: ctx.state,
        referenced_resources: ctx.referenced_resources.insert(src_res).insert(dst_res),
        command_log: ctx.command_log.push(RecordedCommand::CopyBuffer { src_buffer: src, dst_buffer: dst }),
        barrier_log: ctx.barrier_log,
    }
}

/// Record a copy-image command: append to the log and add both resource ids.
pub open spec fn record_copy_image(
    ctx: RecordingContext,
    src: nat,
    dst: nat,
    src_res: ResourceId,
    dst_res: ResourceId,
) -> RecordingContext {
    RecordingContext {
        state: ctx.state,
        referenced_resources: ctx.referenced_resources.insert(src_res).insert(dst_res),
        command_log: ctx.command_log.push(RecordedCommand::CopyImage { src_image: src, dst_image: dst }),
        barrier_log: ctx.barrier_log,
    }
}

/// Record a blit-image command: append to the log and add both resource ids.
pub open spec fn record_blit_image(
    ctx: RecordingContext,
    src: nat,
    dst: nat,
    src_res: ResourceId,
    dst_res: ResourceId,
) -> RecordingContext {
    RecordingContext {
        state: ctx.state,
        referenced_resources: ctx.referenced_resources.insert(src_res).insert(dst_res),
        command_log: ctx.command_log.push(RecordedCommand::BlitImage { src_image: src, dst_image: dst }),
        barrier_log: ctx.barrier_log,
    }
}

/// Record a buffer-to-image copy: append to the log and add both resource ids.
pub open spec fn record_copy_buffer_to_image(
    ctx: RecordingContext,
    src_buffer: nat,
    dst_image: nat,
    src_res: ResourceId,
    dst_res: ResourceId,
) -> RecordingContext {
    RecordingContext {
        state: ctx.state,
        referenced_resources: ctx.referenced_resources.insert(src_res).insert(dst_res),
        command_log: ctx.command_log.push(RecordedCommand::CopyBufferToImage { src_buffer, dst_image }),
        barrier_log: ctx.barrier_log,
    }
}

/// Record an image-to-buffer copy: append to the log and add both resource ids.
pub open spec fn record_copy_image_to_buffer(
    ctx: RecordingContext,
    src_image: nat,
    dst_buffer: nat,
    src_res: ResourceId,
    dst_res: ResourceId,
) -> RecordingContext {
    RecordingContext {
        state: ctx.state,
        referenced_resources: ctx.referenced_resources.insert(src_res).insert(dst_res),
        command_log: ctx.command_log.push(RecordedCommand::CopyImageToBuffer { src_image, dst_buffer }),
        barrier_log: ctx.barrier_log,
    }
}

/// Record an indirect draw command: append to the log and accumulate resources.
pub open spec fn record_draw_indirect(
    ctx: RecordingContext,
    buffer: nat,
    offset: nat,
    draw_count: nat,
    resources: Set<ResourceId>,
) -> RecordingContext {
    RecordingContext {
        state: ctx.state,
        referenced_resources: ctx.referenced_resources.union(resources),
        command_log: ctx.command_log.push(RecordedCommand::DrawIndirect { buffer, offset, draw_count }),
        barrier_log: ctx.barrier_log,
    }
}

/// Record an indirect indexed draw command: append to the log and accumulate resources.
pub open spec fn record_draw_indexed_indirect(
    ctx: RecordingContext,
    buffer: nat,
    offset: nat,
    draw_count: nat,
    resources: Set<ResourceId>,
) -> RecordingContext {
    RecordingContext {
        state: ctx.state,
        referenced_resources: ctx.referenced_resources.union(resources),
        command_log: ctx.command_log.push(RecordedCommand::DrawIndexedIndirect { buffer, offset, draw_count }),
        barrier_log: ctx.barrier_log,
    }
}

/// Record an indirect dispatch command: append to the log and accumulate resources.
pub open spec fn record_dispatch_indirect(
    ctx: RecordingContext,
    buffer: nat,
    offset: nat,
    resources: Set<ResourceId>,
) -> RecordingContext {
    RecordingContext {
        state: ctx.state,
        referenced_resources: ctx.referenced_resources.union(resources),
        command_log: ctx.command_log.push(RecordedCommand::DispatchIndirect { buffer, offset }),
        barrier_log: ctx.barrier_log,
    }
}

/// Record begin dynamic rendering: append to the log.
pub open spec fn record_begin_rendering(
    ctx: RecordingContext,
    info: DynamicRenderingInfo,
) -> RecordingContext {
    RecordingContext {
        state: ctx.state,
        referenced_resources: ctx.referenced_resources,
        command_log: ctx.command_log.push(RecordedCommand::BeginRendering { info }),
        barrier_log: ctx.barrier_log,
    }
}

/// Record end dynamic rendering: append to the log.
pub open spec fn record_end_rendering(
    ctx: RecordingContext,
) -> RecordingContext {
    RecordingContext {
        state: ctx.state,
        referenced_resources: ctx.referenced_resources,
        command_log: ctx.command_log.push(RecordedCommand::EndRendering),
        barrier_log: ctx.barrier_log,
    }
}

/// Record a pipeline barrier with a single entry: appends the entry to the barrier log.
pub open spec fn record_pipeline_barrier_single(
    ctx: RecordingContext,
    entry: BarrierEntry,
) -> RecordingContext {
    RecordingContext {
        barrier_log: ctx.barrier_log.push(entry),
        command_log: ctx.command_log.push(RecordedCommand::PipelineBarrier { barriers: seq![entry] }),
        ..ctx
    }
}

/// Record a pipeline barrier with multiple entries: appends all to the barrier log.
pub open spec fn record_pipeline_barrier(
    ctx: RecordingContext,
    barriers: Seq<BarrierEntry>,
) -> RecordingContext
    decreases barriers.len(),
{
    if barriers.len() == 0 {
        RecordingContext {
            command_log: ctx.command_log.push(RecordedCommand::PipelineBarrier { barriers }),
            ..ctx
        }
    } else if barriers.len() == 1 {
        record_pipeline_barrier_single(ctx, barriers[0])
    } else {
        let prev = record_pipeline_barrier(ctx, barriers.subrange(0, barriers.len() - 1));
        RecordingContext {
            barrier_log: prev.barrier_log.push(barriers.last()),
            command_log: ctx.command_log.push(RecordedCommand::PipelineBarrier { barriers }),
            ..prev
        }
    }
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// full_draw_call_valid implies draw_call_valid.
pub proof fn lemma_full_draw_implies_draw_valid(
    ctx: RecordingContext,
    pipeline: GraphicsPipelineState,
    rp: RenderPassState,
)
    requires full_draw_call_valid(ctx, pipeline, rp),
    ensures draw_call_valid(ctx.state, pipeline, rp),
{
}

/// full_draw_call_valid implies descriptor_sets_bound_for_pipeline.
pub proof fn lemma_full_draw_implies_descriptors_bound(
    ctx: RecordingContext,
    pipeline: GraphicsPipelineState,
    rp: RenderPassState,
)
    requires full_draw_call_valid(ctx, pipeline, rp),
    ensures descriptor_sets_bound_for_pipeline(ctx.state, pipeline.descriptor_set_layouts),
{
}

/// Recording a draw does not change the recording state.
pub proof fn lemma_record_draw_preserves_state(
    ctx: RecordingContext,
    resources: Set<ResourceId>,
)
    ensures record_draw(ctx, resources).state == ctx.state,
{
}

/// After record_draw, referenced_resources is a superset of both old and new resources.
pub proof fn lemma_record_accumulates_resources(
    ctx: RecordingContext,
    resources: Set<ResourceId>,
)
    ensures
        forall|r: ResourceId|
            ctx.referenced_resources.contains(r)
            ==> record_draw(ctx, resources).referenced_resources.contains(r),
        forall|r: ResourceId|
            resources.contains(r)
            ==> record_draw(ctx, resources).referenced_resources.contains(r),
{
}

// ── Transfer / Indirect / Dynamic Rendering Record Proofs ───────────────

/// Recording a copy-image preserves state and barrier_log.
pub proof fn lemma_record_copy_image_preserves(
    ctx: RecordingContext, src: nat, dst: nat,
    src_res: ResourceId, dst_res: ResourceId,
)
    ensures
        record_copy_image(ctx, src, dst, src_res, dst_res).state == ctx.state,
        record_copy_image(ctx, src, dst, src_res, dst_res).barrier_log == ctx.barrier_log,
{
}

/// Recording a blit-image preserves state and barrier_log.
pub proof fn lemma_record_blit_image_preserves(
    ctx: RecordingContext, src: nat, dst: nat,
    src_res: ResourceId, dst_res: ResourceId,
)
    ensures
        record_blit_image(ctx, src, dst, src_res, dst_res).state == ctx.state,
        record_blit_image(ctx, src, dst, src_res, dst_res).barrier_log == ctx.barrier_log,
{
}

/// Recording an indirect draw preserves state and barrier_log.
pub proof fn lemma_record_draw_indirect_preserves(
    ctx: RecordingContext, buffer: nat, offset: nat,
    draw_count: nat, resources: Set<ResourceId>,
)
    ensures
        record_draw_indirect(ctx, buffer, offset, draw_count, resources).state == ctx.state,
        record_draw_indirect(ctx, buffer, offset, draw_count, resources).barrier_log == ctx.barrier_log,
{
}

/// Recording an indirect indexed draw preserves state and barrier_log.
pub proof fn lemma_record_draw_indexed_indirect_preserves(
    ctx: RecordingContext, buffer: nat, offset: nat,
    draw_count: nat, resources: Set<ResourceId>,
)
    ensures
        record_draw_indexed_indirect(ctx, buffer, offset, draw_count, resources).state == ctx.state,
        record_draw_indexed_indirect(ctx, buffer, offset, draw_count, resources).barrier_log == ctx.barrier_log,
{
}

/// Recording an indirect dispatch preserves state and barrier_log.
pub proof fn lemma_record_dispatch_indirect_preserves(
    ctx: RecordingContext, buffer: nat, offset: nat,
    resources: Set<ResourceId>,
)
    ensures
        record_dispatch_indirect(ctx, buffer, offset, resources).state == ctx.state,
        record_dispatch_indirect(ctx, buffer, offset, resources).barrier_log == ctx.barrier_log,
{
}

/// Recording begin rendering preserves state and barrier_log.
pub proof fn lemma_record_begin_rendering_preserves(
    ctx: RecordingContext, info: DynamicRenderingInfo,
)
    ensures
        record_begin_rendering(ctx, info).state == ctx.state,
        record_begin_rendering(ctx, info).barrier_log == ctx.barrier_log,
{
}

/// Recording end rendering preserves state and barrier_log.
pub proof fn lemma_record_end_rendering_preserves(
    ctx: RecordingContext,
)
    ensures
        record_end_rendering(ctx).state == ctx.state,
        record_end_rendering(ctx).barrier_log == ctx.barrier_log,
{
}

// ── New Recording Spec Functions ─────────────────────────────────────

/// Record a fill-buffer command.
pub open spec fn record_fill_buffer(
    ctx: RecordingContext,
    buffer: nat,
    offset: nat,
    size: nat,
    res: ResourceId,
) -> RecordingContext {
    RecordingContext {
        state: ctx.state,
        referenced_resources: ctx.referenced_resources.insert(res),
        command_log: ctx.command_log.push(RecordedCommand::FillBuffer { buffer, offset, size }),
        barrier_log: ctx.barrier_log,
    }
}

/// Record an update-buffer command.
pub open spec fn record_update_buffer(
    ctx: RecordingContext,
    buffer: nat,
    offset: nat,
    size: nat,
    res: ResourceId,
) -> RecordingContext {
    RecordingContext {
        state: ctx.state,
        referenced_resources: ctx.referenced_resources.insert(res),
        command_log: ctx.command_log.push(RecordedCommand::UpdateBuffer { buffer, offset, size }),
        barrier_log: ctx.barrier_log,
    }
}

/// Record a clear-color-image command.
pub open spec fn record_clear_color_image(
    ctx: RecordingContext,
    image: nat,
    res: ResourceId,
) -> RecordingContext {
    RecordingContext {
        state: ctx.state,
        referenced_resources: ctx.referenced_resources.insert(res),
        command_log: ctx.command_log.push(RecordedCommand::ClearColorImage { image }),
        barrier_log: ctx.barrier_log,
    }
}

/// Record a clear-depth-stencil-image command.
pub open spec fn record_clear_depth_stencil_image(
    ctx: RecordingContext,
    image: nat,
    res: ResourceId,
) -> RecordingContext {
    RecordingContext {
        state: ctx.state,
        referenced_resources: ctx.referenced_resources.insert(res),
        command_log: ctx.command_log.push(RecordedCommand::ClearDepthStencilImage { image }),
        barrier_log: ctx.barrier_log,
    }
}

/// Record a clear-attachments command (inside a render pass).
pub open spec fn record_clear_attachments(
    ctx: RecordingContext,
) -> RecordingContext {
    RecordingContext {
        state: ctx.state,
        referenced_resources: ctx.referenced_resources,
        command_log: ctx.command_log.push(RecordedCommand::ClearAttachments),
        barrier_log: ctx.barrier_log,
    }
}

/// Record a resolve-image command.
pub open spec fn record_resolve_image(
    ctx: RecordingContext,
    src: nat,
    dst: nat,
    src_res: ResourceId,
    dst_res: ResourceId,
) -> RecordingContext {
    RecordingContext {
        state: ctx.state,
        referenced_resources: ctx.referenced_resources.insert(src_res).insert(dst_res),
        command_log: ctx.command_log.push(RecordedCommand::ResolveImage { src_image: src, dst_image: dst }),
        barrier_log: ctx.barrier_log,
    }
}

/// Record a write-timestamp command.
pub open spec fn record_write_timestamp(
    ctx: RecordingContext,
    pool_id: nat,
    query: nat,
) -> RecordingContext {
    RecordingContext {
        state: ctx.state,
        referenced_resources: ctx.referenced_resources,
        command_log: ctx.command_log.push(RecordedCommand::WriteTimestamp { pool_id, query }),
        barrier_log: ctx.barrier_log,
    }
}

/// Record a copy-query-pool-results command.
pub open spec fn record_copy_query_pool_results(
    ctx: RecordingContext,
    pool_id: nat,
    first_query: nat,
    query_count: nat,
    dst_buffer: nat,
    dst_res: ResourceId,
) -> RecordingContext {
    RecordingContext {
        state: ctx.state,
        referenced_resources: ctx.referenced_resources.insert(dst_res),
        command_log: ctx.command_log.push(RecordedCommand::CopyQueryPoolResults { pool_id, first_query, query_count, dst_buffer }),
        barrier_log: ctx.barrier_log,
    }
}

/// Record a wait-events command (pushes barrier entry like pipeline_barrier).
pub open spec fn record_wait_events_single(
    ctx: RecordingContext,
    entry: BarrierEntry,
) -> RecordingContext {
    RecordingContext {
        barrier_log: ctx.barrier_log.push(entry),
        command_log: ctx.command_log.push(RecordedCommand::WaitEvents { barriers: seq![entry] }),
        ..ctx
    }
}

/// Record an indirect draw with count command.
pub open spec fn record_draw_indirect_count(
    ctx: RecordingContext,
    buffer: nat,
    offset: nat,
    count_buffer: nat,
    count_offset: nat,
    max_draw_count: nat,
    resources: Set<ResourceId>,
) -> RecordingContext {
    RecordingContext {
        state: ctx.state,
        referenced_resources: ctx.referenced_resources.union(resources),
        command_log: ctx.command_log.push(RecordedCommand::DrawIndirectCount { buffer, offset, count_buffer, count_offset, max_draw_count }),
        barrier_log: ctx.barrier_log,
    }
}

/// Record an indirect indexed draw with count command.
pub open spec fn record_draw_indexed_indirect_count(
    ctx: RecordingContext,
    buffer: nat,
    offset: nat,
    count_buffer: nat,
    count_offset: nat,
    max_draw_count: nat,
    resources: Set<ResourceId>,
) -> RecordingContext {
    RecordingContext {
        state: ctx.state,
        referenced_resources: ctx.referenced_resources.union(resources),
        command_log: ctx.command_log.push(RecordedCommand::DrawIndexedIndirectCount { buffer, offset, count_buffer, count_offset, max_draw_count }),
        barrier_log: ctx.barrier_log,
    }
}

/// Record a trace rays command.
pub open spec fn record_trace_rays(
    ctx: RecordingContext,
    resources: Set<ResourceId>,
) -> RecordingContext {
    RecordingContext {
        state: ctx.state,
        referenced_resources: ctx.referenced_resources.union(resources),
        command_log: ctx.command_log.push(RecordedCommand::TraceRays),
        barrier_log: ctx.barrier_log,
    }
}

/// Record a trace rays indirect command.
pub open spec fn record_trace_rays_indirect(
    ctx: RecordingContext,
    buffer: nat,
    resources: Set<ResourceId>,
) -> RecordingContext {
    RecordingContext {
        state: ctx.state,
        referenced_resources: ctx.referenced_resources.union(resources),
        command_log: ctx.command_log.push(RecordedCommand::TraceRaysIndirect { buffer }),
        barrier_log: ctx.barrier_log,
    }
}

/// Record a dispatch base command.
pub open spec fn record_dispatch_base(
    ctx: RecordingContext,
    base_x: nat, base_y: nat, base_z: nat,
    group_x: nat, group_y: nat, group_z: nat,
    resources: Set<ResourceId>,
) -> RecordingContext {
    RecordingContext {
        state: ctx.state,
        referenced_resources: ctx.referenced_resources.union(resources),
        command_log: ctx.command_log.push(RecordedCommand::DispatchBase { base_x, base_y, base_z, group_x, group_y, group_z }),
        barrier_log: ctx.barrier_log,
    }
}

/// Record a draw mesh tasks command.
pub open spec fn record_draw_mesh_tasks(
    ctx: RecordingContext,
    group_count_x: nat, group_count_y: nat, group_count_z: nat,
    resources: Set<ResourceId>,
) -> RecordingContext {
    RecordingContext {
        state: ctx.state,
        referenced_resources: ctx.referenced_resources.union(resources),
        command_log: ctx.command_log.push(RecordedCommand::DrawMeshTasks { group_count_x, group_count_y, group_count_z }),
        barrier_log: ctx.barrier_log,
    }
}

/// Record a draw mesh tasks indirect command.
pub open spec fn record_draw_mesh_tasks_indirect(
    ctx: RecordingContext,
    buffer: nat, offset: nat, draw_count: nat,
    resources: Set<ResourceId>,
) -> RecordingContext {
    RecordingContext {
        state: ctx.state,
        referenced_resources: ctx.referenced_resources.union(resources),
        command_log: ctx.command_log.push(RecordedCommand::DrawMeshTasksIndirect { buffer, offset, draw_count }),
        barrier_log: ctx.barrier_log,
    }
}

/// Record a draw mesh tasks indirect count command.
pub open spec fn record_draw_mesh_tasks_indirect_count(
    ctx: RecordingContext,
    buffer: nat, offset: nat, count_buffer: nat, count_offset: nat, max_draw_count: nat,
    resources: Set<ResourceId>,
) -> RecordingContext {
    RecordingContext {
        state: ctx.state,
        referenced_resources: ctx.referenced_resources.union(resources),
        command_log: ctx.command_log.push(RecordedCommand::DrawMeshTasksIndirectCount { buffer, offset, count_buffer, count_offset, max_draw_count }),
        barrier_log: ctx.barrier_log,
    }
}

/// Record begin transform feedback.
pub open spec fn record_begin_transform_feedback(
    ctx: RecordingContext,
) -> RecordingContext {
    RecordingContext {
        state: ctx.state,
        referenced_resources: ctx.referenced_resources,
        command_log: ctx.command_log.push(RecordedCommand::BeginTransformFeedback),
        barrier_log: ctx.barrier_log,
    }
}

/// Record end transform feedback.
pub open spec fn record_end_transform_feedback(
    ctx: RecordingContext,
) -> RecordingContext {
    RecordingContext {
        state: ctx.state,
        referenced_resources: ctx.referenced_resources,
        command_log: ctx.command_log.push(RecordedCommand::EndTransformFeedback),
        barrier_log: ctx.barrier_log,
    }
}

/// Record a pipeline barrier 2 (pushes barrier entry, same as pipeline_barrier).
pub open spec fn record_pipeline_barrier2_single(
    ctx: RecordingContext,
    entry: BarrierEntry,
) -> RecordingContext {
    RecordingContext {
        barrier_log: ctx.barrier_log.push(entry),
        command_log: ctx.command_log.push(RecordedCommand::PipelineBarrier2 { barriers: seq![entry] }),
        ..ctx
    }
}

// ── Barrier Proofs ──────────────────────────────────────────────────────

/// After recording a single-entry barrier that covers a last write,
/// the resource becomes readable in the updated context.
pub proof fn lemma_barrier_establishes_readable(
    ctx: RecordingContext,
    entry: BarrierEntry,
    state: SyncState,
    dst_stage: nat,
    dst_access: nat,
)
    requires
        state.last_write.is_some(),
        resource_overlap(entry.resource, state.resource),
        stages_subset(state.write_stages, entry.src_stages),
        access_subset(state.write_accesses, entry.src_accesses),
        entry.dst_stages.stages.contains(dst_stage),
        entry.dst_accesses.accesses.contains(dst_access),
    ensures
        readable(
            record_pipeline_barrier_single(ctx, entry).barrier_log,
            state,
            dst_stage,
            dst_access,
        ),
{
    // record_pipeline_barrier_single directly gives barrier_log = ctx.barrier_log.push(entry)
    lemma_barrier_makes_readable(ctx.barrier_log, state, entry, dst_stage, dst_access);
}

/// After recording a single-entry barrier that covers both last write and readers,
/// the resource becomes writable in the updated context.
pub proof fn lemma_barrier_establishes_writable(
    ctx: RecordingContext,
    entry: BarrierEntry,
    state: SyncState,
    dst_stage: nat,
    dst_access: nat,
)
    requires
        state.last_write.is_some() || state.last_reads.len() > 0,
        resource_overlap(entry.resource, state.resource),
        stages_subset(state.write_stages, entry.src_stages),
        access_subset(state.write_accesses, entry.src_accesses),
        stages_subset(state.read_stages, entry.src_stages),
        access_subset(state.read_accesses, entry.src_accesses),
        entry.dst_stages.stages.contains(dst_stage),
        entry.dst_accesses.accesses.contains(dst_access),
    ensures
        writable(
            record_pipeline_barrier_single(ctx, entry).barrier_log,
            state,
            dst_stage,
            dst_access,
        ),
{
    lemma_barrier_makes_writable(ctx.barrier_log, state, entry, dst_stage, dst_access);
}

/// Recording a single-entry barrier does not change the recording state.
pub proof fn lemma_barrier_single_preserves_state(
    ctx: RecordingContext,
    entry: BarrierEntry,
)
    ensures record_pipeline_barrier_single(ctx, entry).state == ctx.state,
{
}

/// Recording a multi-entry barrier does not change the recording state.
pub proof fn lemma_barrier_preserves_state(
    ctx: RecordingContext,
    barriers: Seq<BarrierEntry>,
)
    ensures record_pipeline_barrier(ctx, barriers).state == ctx.state,
    decreases barriers.len(),
{
    if barriers.len() > 1 {
        lemma_barrier_preserves_state(ctx, barriers.subrange(0, barriers.len() - 1));
    }
}

/// Recording a single-entry barrier preserves referenced_resources.
pub proof fn lemma_barrier_single_preserves_resources(
    ctx: RecordingContext,
    entry: BarrierEntry,
)
    ensures record_pipeline_barrier_single(ctx, entry).referenced_resources == ctx.referenced_resources,
{
}

/// Recording a multi-entry barrier preserves referenced_resources.
pub proof fn lemma_barrier_preserves_resources(
    ctx: RecordingContext,
    barriers: Seq<BarrierEntry>,
)
    ensures record_pipeline_barrier(ctx, barriers).referenced_resources == ctx.referenced_resources,
    decreases barriers.len(),
{
    if barriers.len() > 1 {
        lemma_barrier_preserves_resources(ctx, barriers.subrange(0, barriers.len() - 1));
    }
}

// ── Stage/Access Validity Tracking ──────────────────────────────────

/// All barriers recorded in a context have valid stage/access combinations.
pub open spec fn recording_barriers_valid(ctx: RecordingContext) -> bool {
    all_barriers_valid(ctx.barrier_log)
}

/// The initial recording context has valid barriers (empty log).
pub proof fn lemma_initial_context_barriers_valid()
    ensures recording_barriers_valid(initial_recording_context()),
{
    lemma_empty_log_valid();
}

/// Recording a single valid barrier preserves barrier validity.
pub proof fn lemma_record_barrier_single_preserves_validity(
    ctx: RecordingContext,
    entry: BarrierEntry,
)
    requires
        recording_barriers_valid(ctx),
        barrier_stage_access_valid(entry),
    ensures
        recording_barriers_valid(record_pipeline_barrier_single(ctx, entry)),
{
    lemma_append_valid_barrier(ctx.barrier_log, entry);
}

/// Recording multiple valid barriers preserves barrier validity.
pub proof fn lemma_record_barrier_multi_preserves_validity(
    ctx: RecordingContext,
    barriers: Seq<BarrierEntry>,
)
    requires
        recording_barriers_valid(ctx),
        forall|i: int| 0 <= i < barriers.len()
            ==> barrier_stage_access_valid(#[trigger] barriers[i]),
    ensures
        recording_barriers_valid(record_pipeline_barrier(ctx, barriers)),
    decreases barriers.len(),
{
    if barriers.len() == 0 {
        // Empty barrier: command_log changes but barrier_log unchanged
    } else if barriers.len() == 1 {
        lemma_record_barrier_single_preserves_validity(ctx, barriers[0]);
    } else {
        let prefix = barriers.subrange(0, barriers.len() - 1);
        // prefix elements are valid
        assert forall|i: int| 0 <= i < prefix.len()
        implies barrier_stage_access_valid(#[trigger] prefix[i]) by {
            assert(prefix[i] == barriers[i]);
        }
        lemma_record_barrier_multi_preserves_validity(ctx, prefix);
        let prev = record_pipeline_barrier(ctx, prefix);
        // prev has valid barriers, and barriers.last() is valid
        assert(barrier_stage_access_valid(barriers.last()));
        lemma_append_valid_barrier(prev.barrier_log, barriers.last());
    }
}

} // verus!
