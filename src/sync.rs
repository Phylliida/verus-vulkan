use vstd::prelude::*;
use crate::resource::*;
use crate::flags::*;

verus! {

/// A point in time on a specific queue, used to order operations.
pub struct SyncPoint {
    pub queue_id: nat,
    pub sequence: nat,
}

/// Tracks the synchronization state of a single resource.
///
/// `last_write`: the sync point of the most recent write (None if never written).
/// `last_reads`: the set of sync points that have read since the last write.
/// `write_stages`/`write_accesses`: what the last writer used.
/// `read_stages`/`read_accesses`: union of all readers' stages/accesses.
pub struct SyncState {
    pub resource: ResourceId,
    pub last_write: Option<SyncPoint>,
    pub last_reads: Seq<SyncPoint>,
    pub write_stages: PipelineStageFlags,
    pub write_accesses: AccessFlags,
    pub read_stages: PipelineStageFlags,
    pub read_accesses: AccessFlags,
}

/// A single barrier entry recorded during command buffer execution.
pub struct BarrierEntry {
    /// The resource this barrier applies to.
    pub resource: ResourceId,
    /// Source stages (what must complete before the barrier).
    pub src_stages: PipelineStageFlags,
    /// Source accesses (what writes are made visible).
    pub src_accesses: AccessFlags,
    /// Destination stages (what waits for the barrier).
    pub dst_stages: PipelineStageFlags,
    /// Destination accesses (what reads/writes are made available).
    pub dst_accesses: AccessFlags,
}

/// A log of barrier entries, appended to during recording.
pub type BarrierLog = Seq<BarrierEntry>;

/// True iff there exists a barrier in `log` that covers a read of `resource`
/// at `dst_stage` — i.e., the barrier's source covers the last write's
/// stages/accesses, and the barrier's destination covers the reader's
/// stage/access.
pub open spec fn barrier_chain_exists_for_read(
    log: BarrierLog,
    state: SyncState,
    dst_stage: nat,
    dst_access: nat,
) -> bool {
    exists|i: nat| #[trigger] barrier_covers_read(log, state, dst_stage, dst_access, i)
}

/// True iff barrier at index `i` covers a read.
pub open spec fn barrier_covers_read(
    log: BarrierLog,
    state: SyncState,
    dst_stage: nat,
    dst_access: nat,
    i: nat,
) -> bool {
    i < log.len()
    && resource_overlap(log[i as int].resource, state.resource)
    // Source side covers last writer
    && stages_subset(state.write_stages, log[i as int].src_stages)
    && access_subset(state.write_accesses, log[i as int].src_accesses)
    // Destination side covers the reader
    && log[i as int].dst_stages.stages.contains(dst_stage)
    && log[i as int].dst_accesses.accesses.contains(dst_access)
}

/// True iff there exists a barrier in `log` that covers a write to `resource`
/// at `dst_stage` — the barrier's source must cover both the last writer
/// AND all readers (WAW + WAR hazards).
pub open spec fn barrier_chain_exists_for_write(
    log: BarrierLog,
    state: SyncState,
    dst_stage: nat,
    dst_access: nat,
) -> bool {
    exists|i: nat| #[trigger] barrier_covers_write(log, state, dst_stage, dst_access, i)
}

/// True iff barrier at index `i` covers a write.
pub open spec fn barrier_covers_write(
    log: BarrierLog,
    state: SyncState,
    dst_stage: nat,
    dst_access: nat,
    i: nat,
) -> bool {
    i < log.len()
    && resource_overlap(log[i as int].resource, state.resource)
    // Source covers last writer (WAW)
    && stages_subset(state.write_stages, log[i as int].src_stages)
    && access_subset(state.write_accesses, log[i as int].src_accesses)
    // Source covers all readers (WAR)
    && stages_subset(state.read_stages, log[i as int].src_stages)
    && access_subset(state.read_accesses, log[i as int].src_accesses)
    // Destination covers the new writer
    && log[i as int].dst_stages.stages.contains(dst_stage)
    && log[i as int].dst_accesses.accesses.contains(dst_access)
}

/// A resource is readable at (dst_stage, dst_access) if either:
/// 1. It has never been written (last_write == None), or
/// 2. A covering barrier exists.
pub open spec fn readable(
    log: BarrierLog,
    state: SyncState,
    dst_stage: nat,
    dst_access: nat,
) -> bool {
    state.last_write.is_none()
    || barrier_chain_exists_for_read(log, state, dst_stage, dst_access)
}

/// A resource is writable at (dst_stage, dst_access) if either:
/// 1. It has never been written AND has no readers, or
/// 2. A covering barrier exists for both WAW and WAR.
pub open spec fn writable(
    log: BarrierLog,
    state: SyncState,
    dst_stage: nat,
    dst_access: nat,
) -> bool {
    (state.last_write.is_none() && state.last_reads.len() == 0)
    || barrier_chain_exists_for_write(log, state, dst_stage, dst_access)
}

/// A resource has no synchronization hazard for reading if readable.
pub open spec fn no_read_hazard(
    log: BarrierLog,
    state: SyncState,
    dst_stage: nat,
    dst_access: nat,
) -> bool {
    readable(log, state, dst_stage, dst_access)
}

/// A resource has no synchronization hazard for writing if writable.
pub open spec fn no_write_hazard(
    log: BarrierLog,
    state: SyncState,
    dst_stage: nat,
    dst_access: nat,
) -> bool {
    writable(log, state, dst_stage, dst_access)
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// A resource with no write history and no readers is always writable.
pub proof fn lemma_fresh_resource_writable(
    log: BarrierLog, state: SyncState, dst_stage: nat, dst_access: nat,
)
    requires state.last_write.is_none(), state.last_reads.len() == 0,
    ensures writable(log, state, dst_stage, dst_access),
{
}

/// no_read_hazard is equivalent to readable.
pub proof fn lemma_no_read_hazard_iff_readable(
    log: BarrierLog, state: SyncState, dst_stage: nat, dst_access: nat,
)
    ensures no_read_hazard(log, state, dst_stage, dst_access) == readable(log, state, dst_stage, dst_access),
{
}

/// no_write_hazard is equivalent to writable.
pub proof fn lemma_no_write_hazard_iff_writable(
    log: BarrierLog, state: SyncState, dst_stage: nat, dst_access: nat,
)
    ensures no_write_hazard(log, state, dst_stage, dst_access) == writable(log, state, dst_stage, dst_access),
{
}

/// Writable implies readable (stronger synchronization implies weaker).
pub proof fn lemma_writable_implies_readable(
    log: BarrierLog, state: SyncState, dst_stage: nat, dst_access: nat,
)
    requires writable(log, state, dst_stage, dst_access),
    ensures readable(log, state, dst_stage, dst_access),
{
    if state.last_write.is_none() && state.last_reads.len() == 0 {
        // No writes → readable by first disjunct
    } else {
        // barrier_covers_write subsumes barrier_covers_read
        let i: nat = choose|i: nat| barrier_covers_write(log, state, dst_stage, dst_access, i);
        assert(barrier_covers_read(log, state, dst_stage, dst_access, i));
    }
}

/// An empty barrier log with no prior write is always readable.
pub proof fn lemma_empty_log_fresh_readable(
    state: SyncState, dst_stage: nat, dst_access: nat,
)
    requires state.last_write.is_none(),
    ensures readable(Seq::<BarrierEntry>::empty(), state, dst_stage, dst_access),
{
}

/// barrier_covers_write implies barrier_covers_read at the same index.
pub proof fn lemma_write_cover_implies_read_cover(
    log: BarrierLog, state: SyncState, dst_stage: nat, dst_access: nat, i: nat,
)
    requires barrier_covers_write(log, state, dst_stage, dst_access, i),
    ensures barrier_covers_read(log, state, dst_stage, dst_access, i),
{
}

// ── Barrier Chain Support ──────────────────────────────────────────────
//
// Vulkan allows synchronization through chains of barriers:
// barrier A (src→mid) + barrier B (mid→dst) = valid sync from src to dst.
// The specs below model 2-hop chains; single barriers are a special case.

/// A 2-barrier chain for read synchronization.
/// Barrier at index `i` covers write→mid, barrier at index `j` covers mid→dst.
pub open spec fn barrier_chain_read_2(
    log: BarrierLog,
    state: SyncState,
    dst_stage: nat,
    dst_access: nat,
    i: nat,
    j: nat,
    mid_stage: nat,
    mid_access: nat,
) -> bool {
    i < log.len() && j < log.len()
    && resource_overlap(log[i as int].resource, state.resource)
    && resource_overlap(log[j as int].resource, state.resource)
    // First barrier: write → mid
    && stages_subset(state.write_stages, log[i as int].src_stages)
    && access_subset(state.write_accesses, log[i as int].src_accesses)
    && log[i as int].dst_stages.stages.contains(mid_stage)
    && log[i as int].dst_accesses.accesses.contains(mid_access)
    // Second barrier: mid → dst
    && log[j as int].src_stages.stages.contains(mid_stage)
    && log[j as int].src_accesses.accesses.contains(mid_access)
    && log[j as int].dst_stages.stages.contains(dst_stage)
    && log[j as int].dst_accesses.accesses.contains(dst_access)
}

/// Whether a 2-barrier chain exists for a read.
pub open spec fn barrier_chain_exists_for_read_2(
    log: BarrierLog,
    state: SyncState,
    dst_stage: nat,
    dst_access: nat,
) -> bool {
    exists|i: nat, j: nat, mid_stage: nat, mid_access: nat|
        #[trigger] barrier_chain_read_2(log, state, dst_stage, dst_access, i, j, mid_stage, mid_access)
}

/// A 2-barrier chain for write synchronization.
/// Must cover both WAW (last write→mid→dst) and WAR (all reads→mid→dst).
pub open spec fn barrier_chain_write_2(
    log: BarrierLog,
    state: SyncState,
    dst_stage: nat,
    dst_access: nat,
    i: nat,
    j: nat,
    mid_stage: nat,
    mid_access: nat,
) -> bool {
    i < log.len() && j < log.len()
    && resource_overlap(log[i as int].resource, state.resource)
    && resource_overlap(log[j as int].resource, state.resource)
    // First barrier covers last writer AND all readers → mid
    && stages_subset(state.write_stages, log[i as int].src_stages)
    && access_subset(state.write_accesses, log[i as int].src_accesses)
    && stages_subset(state.read_stages, log[i as int].src_stages)
    && access_subset(state.read_accesses, log[i as int].src_accesses)
    && log[i as int].dst_stages.stages.contains(mid_stage)
    && log[i as int].dst_accesses.accesses.contains(mid_access)
    // Second barrier: mid → dst
    && log[j as int].src_stages.stages.contains(mid_stage)
    && log[j as int].src_accesses.accesses.contains(mid_access)
    && log[j as int].dst_stages.stages.contains(dst_stage)
    && log[j as int].dst_accesses.accesses.contains(dst_access)
}

/// Whether a 2-barrier chain exists for a write.
pub open spec fn barrier_chain_exists_for_write_2(
    log: BarrierLog,
    state: SyncState,
    dst_stage: nat,
    dst_access: nat,
) -> bool {
    exists|i: nat, j: nat, mid_stage: nat, mid_access: nat|
        #[trigger] barrier_chain_write_2(log, state, dst_stage, dst_access, i, j, mid_stage, mid_access)
}

/// A resource is readable via chain: either never written, single barrier,
/// or 2-barrier chain.
pub open spec fn readable_chained(
    log: BarrierLog,
    state: SyncState,
    dst_stage: nat,
    dst_access: nat,
) -> bool {
    state.last_write.is_none()
    || barrier_chain_exists_for_read(log, state, dst_stage, dst_access)
    || barrier_chain_exists_for_read_2(log, state, dst_stage, dst_access)
}

/// A resource is writable via chain: either fresh with no readers,
/// single barrier, or 2-barrier chain.
pub open spec fn writable_chained(
    log: BarrierLog,
    state: SyncState,
    dst_stage: nat,
    dst_access: nat,
) -> bool {
    (state.last_write.is_none() && state.last_reads.len() == 0)
    || barrier_chain_exists_for_write(log, state, dst_stage, dst_access)
    || barrier_chain_exists_for_write_2(log, state, dst_stage, dst_access)
}

/// Single-barrier readable implies chain-readable (backward compatibility).
pub proof fn lemma_single_implies_chain_read(
    log: BarrierLog,
    state: SyncState,
    dst_stage: nat,
    dst_access: nat,
)
    requires readable(log, state, dst_stage, dst_access),
    ensures readable_chained(log, state, dst_stage, dst_access),
{
}

/// Single-barrier writable implies chain-writable (backward compatibility).
pub proof fn lemma_single_implies_chain_write(
    log: BarrierLog,
    state: SyncState,
    dst_stage: nat,
    dst_access: nat,
)
    requires writable(log, state, dst_stage, dst_access),
    ensures writable_chained(log, state, dst_stage, dst_access),
{
}

/// Chain-writable implies chain-readable.
pub proof fn lemma_chain_writable_implies_chain_readable(
    log: BarrierLog,
    state: SyncState,
    dst_stage: nat,
    dst_access: nat,
)
    requires writable_chained(log, state, dst_stage, dst_access),
    ensures readable_chained(log, state, dst_stage, dst_access),
{
    if state.last_write.is_none() && state.last_reads.len() == 0 {
        // No writes → readable by first disjunct
    } else if barrier_chain_exists_for_write(log, state, dst_stage, dst_access) {
        let i: nat = choose|i: nat| barrier_covers_write(log, state, dst_stage, dst_access, i);
        assert(barrier_covers_read(log, state, dst_stage, dst_access, i));
    } else {
        // 2-barrier chain: write chain subsumes read chain
        let (i, j, ms, ma): (nat, nat, nat, nat) = choose|i: nat, j: nat, ms: nat, ma: nat|
            barrier_chain_write_2(log, state, dst_stage, dst_access, i, j, ms, ma);
        assert(barrier_chain_read_2(log, state, dst_stage, dst_access, i, j, ms, ma));
    }
}

} // verus!
