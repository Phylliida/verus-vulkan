use vstd::prelude::*;
use crate::resource::*;
use crate::recording::*;
use crate::recording_commands::*;
use crate::sync::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// A snapshot of the command buffer recording state at a specific point.
///
/// Ghost checkpoints break long command sequences into phases, so that
/// future verification only needs to reference the checkpoint, not the
/// full history before it. This mirrors the "frame invariant" pattern
/// from verus-topology's construction proofs.
pub struct GhostCheckpoint {
    /// The recording state at checkpoint time.
    pub recording_state: RecordingState,
    /// The accumulated set of referenced resources at checkpoint time.
    pub referenced_resources: Set<ResourceId>,
    /// The barrier log at checkpoint time.
    pub barrier_log: BarrierLog,
    /// A monotonic checkpoint sequence number.
    pub sequence: nat,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// Create a checkpoint from the current recording context.
pub open spec fn checkpoint_from_context(
    ctx: RecordingContext,
    seq_num: nat,
) -> GhostCheckpoint {
    GhostCheckpoint {
        recording_state: ctx.state,
        referenced_resources: ctx.referenced_resources,
        barrier_log: ctx.barrier_log,
        sequence: seq_num,
    }
}

/// A recording context matches a checkpoint (state is identical).
pub open spec fn context_matches_checkpoint(
    ctx: RecordingContext,
    cp: GhostCheckpoint,
) -> bool {
    ctx.state == cp.recording_state
    && ctx.referenced_resources == cp.referenced_resources
    && ctx.barrier_log == cp.barrier_log
}

/// A checkpoint is consistent with a later context: the context's state
/// extends the checkpoint (resources are a superset, barrier log is an extension).
pub open spec fn checkpoint_consistent_with(
    cp: GhostCheckpoint,
    ctx: RecordingContext,
) -> bool {
    // Resources only grow
    cp.referenced_resources.subset_of(ctx.referenced_resources)
    // Barrier log is a prefix of the current log
    && barrier_log_extends(cp.barrier_log, ctx.barrier_log)
}

/// True iff `prefix` is a prefix of `full` (same elements at same indices).
pub open spec fn barrier_log_extends(prefix: BarrierLog, full: BarrierLog) -> bool {
    prefix.len() <= full.len()
    && (forall|i: nat| i < prefix.len()
        ==> prefix[i as int] == full[i as int])
}

/// A checkpoint taken at the current context trivially matches.
pub open spec fn take_checkpoint(ctx: RecordingContext, seq_num: nat) -> (GhostCheckpoint, RecordingContext) {
    (checkpoint_from_context(ctx, seq_num), ctx)
}

/// Two checkpoints are ordered: cp1 was taken before cp2.
pub open spec fn checkpoint_ordered(cp1: GhostCheckpoint, cp2: GhostCheckpoint) -> bool {
    cp1.sequence < cp2.sequence
}

/// A barrier that was readable at checkpoint time is still readable in any
/// context consistent with that checkpoint (barrier log only grows).
pub open spec fn readable_at_checkpoint(
    cp: GhostCheckpoint,
    state: SyncState,
    dst_stage: nat,
    dst_access: nat,
) -> bool {
    readable(cp.barrier_log, state, dst_stage, dst_access)
}

/// Consecutive checkpoints: cp2 extends cp1.
pub open spec fn consecutive_checkpoints(
    cp1: GhostCheckpoint,
    cp2: GhostCheckpoint,
) -> bool {
    checkpoint_ordered(cp1, cp2)
    && cp1.referenced_resources.subset_of(cp2.referenced_resources)
    && barrier_log_extends(cp1.barrier_log, cp2.barrier_log)
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// A checkpoint taken from a context matches that context.
pub proof fn lemma_checkpoint_matches_self(ctx: RecordingContext, seq_num: nat)
    ensures
        context_matches_checkpoint(ctx, checkpoint_from_context(ctx, seq_num)),
{
}

/// A checkpoint is consistent with the context it was taken from.
pub proof fn lemma_checkpoint_consistent_with_self(ctx: RecordingContext, seq_num: nat)
    ensures
        checkpoint_consistent_with(checkpoint_from_context(ctx, seq_num), ctx),
{
    let cp = checkpoint_from_context(ctx, seq_num);
    // Resources: ctx.referenced_resources ⊆ ctx.referenced_resources (reflexive)
    // Barrier log: ctx.barrier_log is a prefix of itself
    assert(barrier_log_extends(cp.barrier_log, ctx.barrier_log));
}

/// barrier_log_extends is reflexive.
pub proof fn lemma_barrier_log_extends_reflexive(log: BarrierLog)
    ensures barrier_log_extends(log, log),
{
}

/// barrier_log_extends is transitive.
pub proof fn lemma_barrier_log_extends_transitive(a: BarrierLog, b: BarrierLog, c: BarrierLog)
    requires
        barrier_log_extends(a, b),
        barrier_log_extends(b, c),
    ensures
        barrier_log_extends(a, c),
{
    assert forall|i: nat| i < a.len()
        implies a[i as int] == c[i as int] by {
        assert(a[i as int] == b[i as int]);
        assert(b[i as int] == c[i as int]);
    }
}

/// Checkpoint consistency is transitive: if cp1 is consistent with ctx1,
/// and ctx1's checkpoint cp2 is consistent with ctx2, then cp1 is
/// consistent with ctx2.
pub proof fn lemma_checkpoint_consistency_transitive(
    cp1: GhostCheckpoint,
    ctx1: RecordingContext,
    cp2: GhostCheckpoint,
    ctx2: RecordingContext,
)
    requires
        checkpoint_consistent_with(cp1, ctx1),
        context_matches_checkpoint(ctx1, cp2),
        checkpoint_consistent_with(cp2, ctx2),
    ensures
        checkpoint_consistent_with(cp1, ctx2),
{
    // Resources: cp1 ⊆ ctx1 == cp2 ⊆ ctx2
    assert(cp1.referenced_resources.subset_of(ctx2.referenced_resources));

    // Barrier log: cp1 prefix of ctx1 == cp2 prefix of ctx2
    assert(barrier_log_extends(cp1.barrier_log, ctx1.barrier_log));
    assert(ctx1.barrier_log == cp2.barrier_log);
    assert(barrier_log_extends(cp1.barrier_log, cp2.barrier_log));
    lemma_barrier_log_extends_transitive(cp1.barrier_log, cp2.barrier_log, ctx2.barrier_log);
}

/// Recording a draw preserves checkpoint consistency.
pub proof fn lemma_record_draw_preserves_checkpoint(
    cp: GhostCheckpoint,
    ctx: RecordingContext,
    resources: Set<ResourceId>,
)
    requires checkpoint_consistent_with(cp, ctx),
    ensures checkpoint_consistent_with(cp, record_draw(ctx, resources)),
{
    let new_ctx = record_draw(ctx, resources);
    // Resources grow (union is superset)
    assert(cp.referenced_resources.subset_of(new_ctx.referenced_resources));
    // Barrier log unchanged by draw
    assert(new_ctx.barrier_log == ctx.barrier_log);
    assert(barrier_log_extends(cp.barrier_log, new_ctx.barrier_log));
}

/// Recording a single barrier preserves checkpoint consistency.
pub proof fn lemma_record_barrier_preserves_checkpoint(
    cp: GhostCheckpoint,
    ctx: RecordingContext,
    entry: BarrierEntry,
)
    requires checkpoint_consistent_with(cp, ctx),
    ensures checkpoint_consistent_with(cp, record_pipeline_barrier_single(ctx, entry)),
{
    let new_ctx = record_pipeline_barrier_single(ctx, entry);
    // Resources unchanged
    assert(new_ctx.referenced_resources == ctx.referenced_resources);
    assert(cp.referenced_resources.subset_of(new_ctx.referenced_resources));

    // Barrier log extended by one entry
    assert(new_ctx.barrier_log == ctx.barrier_log.push(entry));
    assert forall|i: nat| i < cp.barrier_log.len()
        implies cp.barrier_log[i as int] == new_ctx.barrier_log[i as int] by {
        assert(cp.barrier_log[i as int] == ctx.barrier_log[i as int]);
        // push preserves existing elements
        assert(new_ctx.barrier_log[i as int] == ctx.barrier_log[i as int]);
    }
}

/// If a resource was readable at a checkpoint, it remains readable in
/// any consistent later context (barrier log only grows, so existential
/// witnesses are preserved).
pub proof fn lemma_readable_preserved_by_extension(
    cp: GhostCheckpoint,
    ctx: RecordingContext,
    state: SyncState,
    dst_stage: nat,
    dst_access: nat,
)
    requires
        checkpoint_consistent_with(cp, ctx),
        readable_at_checkpoint(cp, state, dst_stage, dst_access),
    ensures
        readable(ctx.barrier_log, state, dst_stage, dst_access),
{
    // readable is: last_write.is_none() || exists barrier
    if state.last_write.is_none() {
        // Trivially readable
    } else {
        // There exists a barrier in cp.barrier_log that covers the read.
        // Since cp.barrier_log is a prefix of ctx.barrier_log, that barrier
        // also exists in ctx.barrier_log at the same index.
        assert(barrier_chain_exists_for_read(cp.barrier_log, state, dst_stage, dst_access));
        let witness = choose|i: nat| barrier_covers_read(cp.barrier_log, state, dst_stage, dst_access, i);
        // The witness barrier is at index `witness` in cp.barrier_log
        assert(witness < cp.barrier_log.len());
        assert(cp.barrier_log[witness as int] == ctx.barrier_log[witness as int]);
        // So the same barrier covers the read in ctx.barrier_log
        assert(barrier_covers_read(ctx.barrier_log, state, dst_stage, dst_access, witness));
    }
}

/// Consecutive checkpoints are transitive.
pub proof fn lemma_consecutive_transitive(
    cp1: GhostCheckpoint,
    cp2: GhostCheckpoint,
    cp3: GhostCheckpoint,
)
    requires
        consecutive_checkpoints(cp1, cp2),
        consecutive_checkpoints(cp2, cp3),
    ensures
        consecutive_checkpoints(cp1, cp3),
{
    assert(cp1.sequence < cp3.sequence);
    assert(cp1.referenced_resources.subset_of(cp3.referenced_resources));
    lemma_barrier_log_extends_transitive(cp1.barrier_log, cp2.barrier_log, cp3.barrier_log);
}

/// The initial recording context has empty state that can serve as
/// a valid initial checkpoint.
pub proof fn lemma_initial_checkpoint_valid()
    ensures ({
        let ctx = initial_recording_context();
        let cp = checkpoint_from_context(ctx, 0);
        context_matches_checkpoint(ctx, cp)
        && cp.referenced_resources == Set::<ResourceId>::empty()
        && cp.barrier_log.len() == 0
    }),
{
}

} // verus!
