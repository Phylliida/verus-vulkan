use vstd::prelude::*;
use crate::sync::*;
use crate::sync_proofs::*;
use crate::flags::*;
use crate::resource::*;
use crate::render_graph::*;
use crate::render_graph_compile::*;

verus! {

// ── Type Bridge ─────────────────────────────────────────────────────────

/// Convert a BarrierAction (render graph compile) to a BarrierEntry (sync).
/// Drops the layout fields, keeping only the synchronization half.
pub open spec fn barrier_action_to_entry(ba: BarrierAction) -> BarrierEntry {
    BarrierEntry {
        resource: ba.resource,
        src_stages: ba.src_stages,
        src_accesses: ba.src_accesses,
        dst_stages: ba.dst_stages,
        dst_accesses: ba.dst_accesses,
    }
}

/// Convert and append a sequence of barrier actions to a barrier log.
pub open spec fn append_barrier_actions(
    log: BarrierLog,
    actions: Seq<BarrierAction>,
) -> BarrierLog
    decreases actions.len(),
{
    if actions.len() == 0 {
        log
    } else {
        append_barrier_actions(
            log.push(barrier_action_to_entry(actions[0])),
            actions.subrange(1, actions.len() as int),
        )
    }
}

/// Collect all pre-barriers from steps 0..step into a single barrier log.
/// Processes barrier plans in execution order.
pub open spec fn collect_pre_barriers(
    cg: CompiledGraph,
    step: nat,
) -> BarrierLog
    recommends step <= cg.barrier_plans.len(),
    decreases step,
{
    if step == 0 {
        Seq::empty()
    } else {
        let prev_log = collect_pre_barriers(cg, (step - 1) as nat);
        append_barrier_actions(
            prev_log,
            cg.barrier_plans[(step - 1) as int].pre_barriers,
        )
    }
}

// ── Adequacy Predicates ─────────────────────────────────────────────────

/// A barrier action covers a read dependency: matching resource, source covers
/// the writer, destination covers the reader's stage/access.
pub open spec fn barrier_action_covers_read(
    ba: BarrierAction,
    state: SyncState,
    dst_stage: nat,
    dst_access: nat,
) -> bool {
    resource_overlap(ba.resource, state.resource)
    && stages_subset(state.write_stages, ba.src_stages)
    && access_subset(state.write_accesses, ba.src_accesses)
    && ba.dst_stages.stages.contains(dst_stage)
    && ba.dst_accesses.accesses.contains(dst_access)
}

/// A barrier action covers a write dependency: matching resource, source covers
/// both the previous writer (WAW) and all readers (WAR), destination covers
/// the new writer's stage/access.
pub open spec fn barrier_action_covers_write(
    ba: BarrierAction,
    state: SyncState,
    dst_stage: nat,
    dst_access: nat,
) -> bool {
    resource_overlap(ba.resource, state.resource)
    && stages_subset(state.write_stages, ba.src_stages)
    && access_subset(state.write_accesses, ba.src_accesses)
    && stages_subset(state.read_stages, ba.src_stages)
    && access_subset(state.read_accesses, ba.src_accesses)
    && ba.dst_stages.stages.contains(dst_stage)
    && ba.dst_accesses.accesses.contains(dst_access)
}

/// A barrier plan is adequate for a read: some pre-barrier covers the read.
pub open spec fn barrier_plan_adequate_for_read(
    plan: PassBarrierPlan,
    state: SyncState,
    dst_stage: nat,
    dst_access: nat,
) -> bool {
    exists|i: nat|
        #![trigger plan.pre_barriers[i as int]]
        i < plan.pre_barriers.len()
        && barrier_action_covers_read(
            plan.pre_barriers[i as int], state, dst_stage, dst_access,
        )
}

/// A barrier plan is adequate for a write: some pre-barrier covers the write.
pub open spec fn barrier_plan_adequate_for_write(
    plan: PassBarrierPlan,
    state: SyncState,
    dst_stage: nat,
    dst_access: nat,
) -> bool {
    exists|i: nat|
        #![trigger plan.pre_barriers[i as int]]
        i < plan.pre_barriers.len()
        && barrier_action_covers_write(
            plan.pre_barriers[i as int], state, dst_stage, dst_access,
        )
}

// ── Per-Step Readable/Writable ──────────────────────────────────────────

/// A resource is readable at a given step in the compiled graph:
/// the accumulated barrier log up to that step establishes readability.
pub open spec fn graph_step_readable(
    cg: CompiledGraph,
    step: nat,
    state: SyncState,
    dst_stage: nat,
    dst_access: nat,
) -> bool {
    readable(collect_pre_barriers(cg, step), state, dst_stage, dst_access)
}

/// A resource is writable at a given step in the compiled graph:
/// the accumulated barrier log up to that step establishes writability.
pub open spec fn graph_step_writable(
    cg: CompiledGraph,
    step: nat,
    state: SyncState,
    dst_stage: nat,
    dst_access: nat,
) -> bool {
    writable(collect_pre_barriers(cg, step), state, dst_stage, dst_access)
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// If a barrier plan has an adequate barrier action for a read,
/// then after appending that plan's pre-barriers, readability holds.
///
/// Key insight: the adequate barrier action at index `i` in pre_barriers
/// becomes a BarrierEntry in the log via barrier_action_to_entry, and
/// barrier_covers_read holds at that log position.
pub proof fn lemma_adequate_barrier_action_establishes_readable(
    log: BarrierLog,
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
            append_barrier_actions(log, plan.pre_barriers),
            state,
            dst_stage,
            dst_access,
        ),
    decreases plan.pre_barriers.len(),
{
    let actions = plan.pre_barriers;
    if actions.len() == 0 {
        // Contradiction: adequacy requires a witness with i < 0
    } else {
        let first_entry = barrier_action_to_entry(actions[0]);
        let new_log = log.push(first_entry);
        let rest = actions.subrange(1, actions.len() as int);

        // Help Z3 unfold: append(log, actions) == append(new_log, rest)
        assert(append_barrier_actions(log, actions)
            == append_barrier_actions(new_log, rest));

        // Check if the first barrier covers the read
        if barrier_action_covers_read(actions[0], state, dst_stage, dst_access) {
            // First barrier covers it — establishes readable on new_log
            lemma_barrier_makes_readable(log, state, first_entry, dst_stage, dst_access);
            // Monotone through the rest
            lemma_append_preserves_readable(new_log, rest, state, dst_stage, dst_access);
        } else {
            // The adequate barrier is in the rest — build adequacy for rest
            let rest_plan = PassBarrierPlan {
                pre_barriers: rest,
                ..plan
            };
            // Prove rest_plan is adequate: the witness must be > 0
            assert(barrier_plan_adequate_for_read(rest_plan, state, dst_stage, dst_access)) by {
                let wit = choose|i: nat|
                    #![trigger plan.pre_barriers[i as int]]
                    i < plan.pre_barriers.len()
                    && barrier_action_covers_read(
                        plan.pre_barriers[i as int], state, dst_stage, dst_access,
                    );
                // wit != 0 since actions[0] doesn't cover
                assert(wit > 0);
                let shifted: nat = (wit - 1) as nat;
                assert(rest[shifted as int] == actions[wit as int]);
                assert(shifted < rest_plan.pre_barriers.len()
                    && barrier_action_covers_read(
                        rest_plan.pre_barriers[shifted as int], state, dst_stage, dst_access,
                    ));
            }
            lemma_adequate_barrier_action_establishes_readable(
                new_log, rest_plan, state, dst_stage, dst_access,
            );
        }
    }
}

/// If a barrier plan has an adequate barrier action for a write,
/// then after appending that plan's pre-barriers, writability holds.
pub proof fn lemma_adequate_barrier_action_establishes_writable(
    log: BarrierLog,
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
            append_barrier_actions(log, plan.pre_barriers),
            state,
            dst_stage,
            dst_access,
        ),
    decreases plan.pre_barriers.len(),
{
    let actions = plan.pre_barriers;
    if actions.len() == 0 {
        // Contradiction
    } else {
        let first_entry = barrier_action_to_entry(actions[0]);
        let new_log = log.push(first_entry);
        let rest = actions.subrange(1, actions.len() as int);

        // Help Z3 unfold
        assert(append_barrier_actions(log, actions)
            == append_barrier_actions(new_log, rest));

        if barrier_action_covers_write(actions[0], state, dst_stage, dst_access) {
            lemma_barrier_makes_writable(log, state, first_entry, dst_stage, dst_access);
            lemma_append_preserves_writable(new_log, rest, state, dst_stage, dst_access);
        } else {
            let rest_plan = PassBarrierPlan {
                pre_barriers: rest,
                ..plan
            };
            assert(barrier_plan_adequate_for_write(rest_plan, state, dst_stage, dst_access)) by {
                let wit = choose|i: nat|
                    #![trigger plan.pre_barriers[i as int]]
                    i < plan.pre_barriers.len()
                    && barrier_action_covers_write(
                        plan.pre_barriers[i as int], state, dst_stage, dst_access,
                    );
                assert(wit > 0);
                let shifted: nat = (wit - 1) as nat;
                assert(rest[shifted as int] == actions[wit as int]);
                assert(shifted < rest_plan.pre_barriers.len()
                    && barrier_action_covers_write(
                        rest_plan.pre_barriers[shifted as int], state, dst_stage, dst_access,
                    ));
            }
            lemma_adequate_barrier_action_establishes_writable(
                new_log, rest_plan, state, dst_stage, dst_access,
            );
        }
    }
}

/// Adding more steps to collect_pre_barriers only grows the log;
/// readability established at step s is preserved at step s+1.
pub proof fn lemma_collect_pre_barriers_monotone(
    cg: CompiledGraph,
    step: nat,
    state: SyncState,
    dst_stage: nat,
    dst_access: nat,
)
    requires
        step > 0,
        readable(
            collect_pre_barriers(cg, (step - 1) as nat),
            state,
            dst_stage,
            dst_access,
        ),
    ensures
        readable(
            collect_pre_barriers(cg, step),
            state,
            dst_stage,
            dst_access,
        ),
{
    let prev_log = collect_pre_barriers(cg, (step - 1) as nat);
    let barriers = cg.barrier_plans[(step - 1) as int].pre_barriers;
    // collect_pre_barriers(cg, step) == append_barrier_actions(prev_log, barriers)
    lemma_append_preserves_readable(prev_log, barriers, state, dst_stage, dst_access);
}

// ── Helper: append preserves readable/writable ──────────────────────

/// Appending barrier actions to a log preserves readability.
proof fn lemma_append_preserves_readable(
    log: BarrierLog,
    actions: Seq<BarrierAction>,
    state: SyncState,
    dst_stage: nat,
    dst_access: nat,
)
    requires readable(log, state, dst_stage, dst_access),
    ensures readable(append_barrier_actions(log, actions), state, dst_stage, dst_access),
    decreases actions.len(),
{
    if actions.len() > 0 {
        let entry = barrier_action_to_entry(actions[0]);
        let new_log = log.push(entry);
        lemma_readable_monotone(log, state, entry, dst_stage, dst_access);
        let rest = actions.subrange(1, actions.len() as int);
        lemma_append_preserves_readable(new_log, rest, state, dst_stage, dst_access);
    }
}

/// Appending barrier actions to a log preserves writability.
proof fn lemma_append_preserves_writable(
    log: BarrierLog,
    actions: Seq<BarrierAction>,
    state: SyncState,
    dst_stage: nat,
    dst_access: nat,
)
    requires writable(log, state, dst_stage, dst_access),
    ensures writable(append_barrier_actions(log, actions), state, dst_stage, dst_access),
    decreases actions.len(),
{
    if actions.len() > 0 {
        let entry = barrier_action_to_entry(actions[0]);
        let new_log = log.push(entry);
        lemma_writable_monotone(log, state, entry, dst_stage, dst_access);
        let rest = actions.subrange(1, actions.len() as int);
        lemma_append_preserves_writable(new_log, rest, state, dst_stage, dst_access);
    }
}

} // verus!
