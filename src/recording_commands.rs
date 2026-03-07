use vstd::prelude::*;
use crate::resource::*;
use crate::recording::*;
use crate::pipeline::*;
use crate::render_pass::*;
use crate::flags::*;
use crate::sync::*;
use crate::sync_proofs::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// A recorded command in the command buffer log.
pub enum RecordedCommand {
    Draw,
    DrawIndexed,
    Dispatch { group_count_x: nat, group_count_y: nat, group_count_z: nat },
    CopyBuffer { src_buffer: nat, dst_buffer: nat },
    BindGraphicsPipeline { pipeline_id: nat },
    BindComputePipeline { pipeline_id: nat },
    BindDescriptorSet { set_index: nat, set_id: nat },
    BeginRenderPass { rp_id: nat, fb_id: nat },
    EndRenderPass,
    NextSubpass,
    PipelineBarrier { barriers: Seq<BarrierEntry> },
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

} // verus!
