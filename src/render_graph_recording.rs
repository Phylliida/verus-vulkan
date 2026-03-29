use vstd::prelude::*;
use crate::sync::*;
use crate::sync_proofs::*;
use crate::flags::*;
use crate::resource::*;
use crate::render_graph::*;
use crate::render_graph_compile::*;
use crate::render_graph_soundness::*;
use crate::recording_commands::*;

verus! {

//  ── Spec Functions ──────────────────────────────────────────────────────

///  Convert a BarrierAction to a BarrierEntry and record it into a RecordingContext.
///  This bridges the render graph compile layer (BarrierAction) to the recording
///  layer (BarrierEntry via record_pipeline_barrier_single).
pub open spec fn barrier_action_to_recording_entry(ba: BarrierAction) -> BarrierEntry {
    barrier_action_to_entry(ba)
}

///  Record all pre-barriers from a PassBarrierPlan into a RecordingContext.
///  Converts each BarrierAction to a BarrierEntry and appends to the barrier log.
pub open spec fn record_barrier_plan(
    ctx: RecordingContext,
    plan: PassBarrierPlan,
) -> RecordingContext
    decreases plan.pre_barriers.len(),
{
    if plan.pre_barriers.len() == 0 {
        ctx
    } else {
        let entry = barrier_action_to_entry(plan.pre_barriers[0]);
        let next_ctx = record_pipeline_barrier_single(ctx, entry);
        let rest_plan = PassBarrierPlan {
            pre_barriers: plan.pre_barriers.subrange(1, plan.pre_barriers.len() as int),
            ..plan
        };
        record_barrier_plan(next_ctx, rest_plan)
    }
}

///  Record one step of a compiled graph: apply pre-barriers for the step.
pub open spec fn record_graph_step(
    ctx: RecordingContext,
    cg: CompiledGraph,
    step: nat,
) -> RecordingContext
    recommends step < cg.barrier_plans.len(),
{
    record_barrier_plan(ctx, cg.barrier_plans[step as int])
}

///  Execute all steps of a compiled graph: fold over steps 0..n,
///  recording each step's pre-barriers.
pub open spec fn execute_compiled_graph(
    cg: CompiledGraph,
    n: nat,
) -> RecordingContext
    decreases n,
{
    if n == 0 {
        initial_recording_context()
    } else {
        let prev = execute_compiled_graph(cg, (n - 1) as nat);
        record_graph_step(prev, cg, (n - 1) as nat)
    }
}

//  ── Proofs ──────────────────────────────────────────────────────────────

///  Recording a barrier plan preserves the RecordingState (bound pipelines, etc.).
pub proof fn lemma_record_barrier_plan_preserves_state(
    ctx: RecordingContext,
    plan: PassBarrierPlan,
)
    ensures record_barrier_plan(ctx, plan).state == ctx.state,
    decreases plan.pre_barriers.len(),
{
    if plan.pre_barriers.len() > 0 {
        let entry = barrier_action_to_entry(plan.pre_barriers[0]);
        let next_ctx = record_pipeline_barrier_single(ctx, entry);
        lemma_barrier_single_preserves_state(ctx, entry);
        let rest_plan = PassBarrierPlan {
            pre_barriers: plan.pre_barriers.subrange(1, plan.pre_barriers.len() as int),
            ..plan
        };
        lemma_record_barrier_plan_preserves_state(next_ctx, rest_plan);
    }
}

///  Recording a barrier plan preserves referenced_resources.
pub proof fn lemma_record_barrier_plan_preserves_resources(
    ctx: RecordingContext,
    plan: PassBarrierPlan,
)
    ensures record_barrier_plan(ctx, plan).referenced_resources == ctx.referenced_resources,
    decreases plan.pre_barriers.len(),
{
    if plan.pre_barriers.len() > 0 {
        let entry = barrier_action_to_entry(plan.pre_barriers[0]);
        let next_ctx = record_pipeline_barrier_single(ctx, entry);
        lemma_barrier_single_preserves_resources(ctx, entry);
        let rest_plan = PassBarrierPlan {
            pre_barriers: plan.pre_barriers.subrange(1, plan.pre_barriers.len() as int),
            ..plan
        };
        lemma_record_barrier_plan_preserves_resources(next_ctx, rest_plan);
    }
}

///  The barrier log after recording a full plan equals the original log
///  with all plan entries appended (via append_barrier_actions).
pub proof fn lemma_record_barrier_plan_log_equals_append(
    ctx: RecordingContext,
    plan: PassBarrierPlan,
)
    ensures
        record_barrier_plan(ctx, plan).barrier_log
            == append_barrier_actions(ctx.barrier_log, plan.pre_barriers),
    decreases plan.pre_barriers.len(),
{
    if plan.pre_barriers.len() == 0 {
        //  Both sides equal ctx.barrier_log
    } else {
        let entry = barrier_action_to_entry(plan.pre_barriers[0]);
        let next_ctx = record_pipeline_barrier_single(ctx, entry);
        let rest = plan.pre_barriers.subrange(1, plan.pre_barriers.len() as int);
        let rest_plan = PassBarrierPlan {
            pre_barriers: rest,
            ..plan
        };
        //  next_ctx.barrier_log == ctx.barrier_log.push(entry)
        //  append(log, actions) == append(log.push(entry), rest) when actions non-empty
        assert(append_barrier_actions(ctx.barrier_log, plan.pre_barriers)
            == append_barrier_actions(ctx.barrier_log.push(entry), rest));
        lemma_record_barrier_plan_log_equals_append(next_ctx, rest_plan);
    }
}

///  If a barrier plan is adequate for a read, recording it establishes
///  readable in the updated recording context.
///
///  Bridges render_graph_soundness::lemma_adequate_barrier_action_establishes_readable
///  to the recording context layer.
pub proof fn lemma_record_barrier_plan_readable(
    ctx: RecordingContext,
    plan: PassBarrierPlan,
    state: SyncState,
    dst_stage: nat,
    dst_access: nat,
)
    requires
        state.last_write.is_some(),
        barrier_plan_adequate_for_read(plan, state, dst_stage, dst_access),
    ensures
        readable(
            record_barrier_plan(ctx, plan).barrier_log,
            state,
            dst_stage,
            dst_access,
        ),
{
    lemma_record_barrier_plan_log_equals_append(ctx, plan);
    lemma_adequate_barrier_action_establishes_readable(
        ctx.barrier_log, plan, state, dst_stage, dst_access,
    );
}

///  If a barrier plan is adequate for a write, recording it establishes
///  writable in the updated recording context.
pub proof fn lemma_record_barrier_plan_writable(
    ctx: RecordingContext,
    plan: PassBarrierPlan,
    state: SyncState,
    dst_stage: nat,
    dst_access: nat,
)
    requires
        state.last_write.is_some() || state.last_reads.len() > 0,
        barrier_plan_adequate_for_write(plan, state, dst_stage, dst_access),
    ensures
        writable(
            record_barrier_plan(ctx, plan).barrier_log,
            state,
            dst_stage,
            dst_access,
        ),
{
    lemma_record_barrier_plan_log_equals_append(ctx, plan);
    lemma_adequate_barrier_action_establishes_writable(
        ctx.barrier_log, plan, state, dst_stage, dst_access,
    );
}

///  Each graph step maintains the sync invariant: recording the step's
///  pre-barriers does not lose any previously established readability.
pub proof fn lemma_graph_step_maintains_sync(
    ctx: RecordingContext,
    cg: CompiledGraph,
    step: nat,
    state: SyncState,
    dst_stage: nat,
    dst_access: nat,
)
    requires
        step < cg.barrier_plans.len(),
        readable(ctx.barrier_log, state, dst_stage, dst_access),
    ensures
        readable(
            record_graph_step(ctx, cg, step).barrier_log,
            state,
            dst_stage,
            dst_access,
        ),
{
    let plan = cg.barrier_plans[step as int];
    lemma_record_barrier_plan_log_equals_append(ctx, plan);
    lemma_append_preserves_readable_via_plan(ctx.barrier_log, plan, state, dst_stage, dst_access);
}

///  Helper: appending a plan's pre-barriers preserves readability (wraps
///  render_graph_soundness helper at the plan level).
proof fn lemma_append_preserves_readable_via_plan(
    log: BarrierLog,
    plan: PassBarrierPlan,
    state: SyncState,
    dst_stage: nat,
    dst_access: nat,
)
    requires readable(log, state, dst_stage, dst_access),
    ensures readable(append_barrier_actions(log, plan.pre_barriers), state, dst_stage, dst_access),
    decreases plan.pre_barriers.len(),
{
    if plan.pre_barriers.len() > 0 {
        let entry = barrier_action_to_entry(plan.pre_barriers[0]);
        let new_log = log.push(entry);
        let rest = plan.pre_barriers.subrange(1, plan.pre_barriers.len() as int);
        lemma_readable_monotone(log, state, entry, dst_stage, dst_access);
        let rest_plan = PassBarrierPlan { pre_barriers: rest, ..plan };
        lemma_append_preserves_readable_via_plan(new_log, rest_plan, state, dst_stage, dst_access);
    }
}

///  A barrier action that is well-formed (non-empty stages/accesses)
///  converts to a valid BarrierEntry with valid stage/access combinations.
pub proof fn lemma_barrier_action_to_entry_valid(
    ba: BarrierAction,
)
    requires barrier_action_well_formed(ba),
    ensures ({
        let entry = barrier_action_to_entry(ba);
        entry.src_stages == ba.src_stages
        && entry.src_accesses == ba.src_accesses
        && entry.dst_stages == ba.dst_stages
        && entry.dst_accesses == ba.dst_accesses
        && entry.resource == ba.resource
    }),
{
}

} //  verus!
