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

} // verus!
