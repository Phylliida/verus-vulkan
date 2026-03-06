use vstd::prelude::*;
use crate::resource::*;
use crate::flags::*;
use crate::sync::*;

verus! {

/// Appending a barrier that covers the last write makes the resource readable.
///
/// Given a barrier entry whose src covers the write stages/accesses and
/// whose dst covers the desired read stage/access, appending it to the log
/// establishes readability.
pub proof fn lemma_barrier_makes_readable(
    log: BarrierLog,
    state: SyncState,
    entry: BarrierEntry,
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
        readable(log.push(entry), state, dst_stage, dst_access),
{
    let new_log = log.push(entry);
    let i: nat = log.len();
    // Witness: the newly appended entry at index log.len()
    assert(barrier_covers_read(new_log, state, dst_stage, dst_access, i));
}

/// Appending a barrier that covers both last write and all reads makes
/// the resource writable.
pub proof fn lemma_barrier_makes_writable(
    log: BarrierLog,
    state: SyncState,
    entry: BarrierEntry,
    dst_stage: nat,
    dst_access: nat,
)
    requires
        state.last_write.is_some() || state.last_reads.len() > 0,
        resource_overlap(entry.resource, state.resource),
        // Covers last writer (WAW)
        stages_subset(state.write_stages, entry.src_stages),
        access_subset(state.write_accesses, entry.src_accesses),
        // Covers all readers (WAR)
        stages_subset(state.read_stages, entry.src_stages),
        access_subset(state.read_accesses, entry.src_accesses),
        entry.dst_stages.stages.contains(dst_stage),
        entry.dst_accesses.accesses.contains(dst_access),
    ensures
        writable(log.push(entry), state, dst_stage, dst_access),
{
    let new_log = log.push(entry);
    let i: nat = log.len();
    // Witness: the newly appended entry
    assert(barrier_covers_write(new_log, state, dst_stage, dst_access, i));
}

/// Resources that have never been written are always readable.
pub proof fn lemma_initial_resources_readable(
    log: BarrierLog,
    state: SyncState,
    dst_stage: nat,
    dst_access: nat,
)
    requires state.last_write.is_none(),
    ensures readable(log, state, dst_stage, dst_access),
{
    // Follows directly from the first disjunct of `readable`.
}

/// Readability implies no read hazard (trivial unfolding).
pub proof fn lemma_readable_implies_no_hazard(
    log: BarrierLog,
    state: SyncState,
    dst_stage: nat,
    dst_access: nat,
)
    requires readable(log, state, dst_stage, dst_access),
    ensures no_read_hazard(log, state, dst_stage, dst_access),
{
    // no_read_hazard is defined as readable — nothing to prove.
}

/// Extending the barrier log preserves readability.
///
/// If a resource is readable with log `log`, it remains readable with
/// `log.push(entry)` for any entry.
pub proof fn lemma_readable_monotone(
    log: BarrierLog,
    state: SyncState,
    entry: BarrierEntry,
    dst_stage: nat,
    dst_access: nat,
)
    requires readable(log, state, dst_stage, dst_access),
    ensures readable(log.push(entry), state, dst_stage, dst_access),
{
    if state.last_write.is_some() {
        // There exists a witness i in log that covers the read.
        // That same i works in log.push(entry) since push only appends.
        let i: nat = choose|i: nat| barrier_covers_read(log, state, dst_stage, dst_access, i);
        let new_log = log.push(entry);
        // The old entry at index i is unchanged in the new log.
        assert(new_log[i as int] == log[i as int]);
        assert(barrier_covers_read(new_log, state, dst_stage, dst_access, i));
    }
    // If last_write is None, readable holds by first disjunct regardless.
}

/// Extending the barrier log preserves writability.
pub proof fn lemma_writable_monotone(
    log: BarrierLog,
    state: SyncState,
    entry: BarrierEntry,
    dst_stage: nat,
    dst_access: nat,
)
    requires writable(log, state, dst_stage, dst_access),
    ensures writable(log.push(entry), state, dst_stage, dst_access),
{
    if state.last_write.is_some() || state.last_reads.len() > 0 {
        // Recover the witness from the old log.
        let i: nat = choose|i: nat| barrier_covers_write(log, state, dst_stage, dst_access, i);
        let new_log = log.push(entry);
        assert(new_log[i as int] == log[i as int]);
        assert(barrier_covers_write(new_log, state, dst_stage, dst_access, i));
    }
    // If never written and no readers, writable holds by first disjunct.
}

} // verus!
