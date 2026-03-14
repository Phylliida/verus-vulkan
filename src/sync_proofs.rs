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

// ── Barrier Chain Proofs ────────────────────────────────────────────────

/// Extending the barrier log preserves chain-readability.
pub proof fn lemma_readable_chained_monotone(
    log: BarrierLog,
    state: SyncState,
    entry: BarrierEntry,
    dst_stage: nat,
    dst_access: nat,
)
    requires readable_chained(log, state, dst_stage, dst_access),
    ensures readable_chained(log.push(entry), state, dst_stage, dst_access),
{
    let new_log = log.push(entry);
    if state.last_write.is_none() {
        // First disjunct carries over
    } else if barrier_chain_exists_for_read(log, state, dst_stage, dst_access) {
        // Single-barrier witness carries over
        let i: nat = choose|i: nat| barrier_covers_read(log, state, dst_stage, dst_access, i);
        assert(new_log[i as int] == log[i as int]);
        assert(barrier_covers_read(new_log, state, dst_stage, dst_access, i));
    } else {
        // 2-barrier chain witness carries over
        let (i, j, ms, ma): (nat, nat, nat, nat) = choose|i: nat, j: nat, ms: nat, ma: nat|
            barrier_chain_read_2(log, state, dst_stage, dst_access, i, j, ms, ma);
        assert(new_log[i as int] == log[i as int]);
        assert(new_log[j as int] == log[j as int]);
        assert(barrier_chain_read_2(new_log, state, dst_stage, dst_access, i, j, ms, ma));
    }
}

/// Extending the barrier log preserves chain-writability.
pub proof fn lemma_writable_chained_monotone(
    log: BarrierLog,
    state: SyncState,
    entry: BarrierEntry,
    dst_stage: nat,
    dst_access: nat,
)
    requires writable_chained(log, state, dst_stage, dst_access),
    ensures writable_chained(log.push(entry), state, dst_stage, dst_access),
{
    let new_log = log.push(entry);
    if state.last_write.is_none() && state.last_reads.len() == 0 {
        // First disjunct carries over
    } else if barrier_chain_exists_for_write(log, state, dst_stage, dst_access) {
        let i: nat = choose|i: nat| barrier_covers_write(log, state, dst_stage, dst_access, i);
        assert(new_log[i as int] == log[i as int]);
        assert(barrier_covers_write(new_log, state, dst_stage, dst_access, i));
    } else {
        let (i, j, ms, ma): (nat, nat, nat, nat) = choose|i: nat, j: nat, ms: nat, ma: nat|
            barrier_chain_write_2(log, state, dst_stage, dst_access, i, j, ms, ma);
        assert(new_log[i as int] == log[i as int]);
        assert(new_log[j as int] == log[j as int]);
        assert(barrier_chain_write_2(new_log, state, dst_stage, dst_access, i, j, ms, ma));
    }
}

/// Two barriers in the log that chain through a midpoint establish readability.
pub proof fn lemma_chain_transitivity_read(
    log: BarrierLog,
    state: SyncState,
    dst_stage: nat,
    dst_access: nat,
    i: nat,
    j: nat,
    mid_stage: nat,
    mid_access: nat,
)
    requires
        state.last_write.is_some(),
        barrier_chain_read_2(log, state, dst_stage, dst_access, i, j, mid_stage, mid_access),
    ensures
        readable_chained(log, state, dst_stage, dst_access),
{
}

/// Two barriers in the log that chain through a midpoint establish writability.
pub proof fn lemma_chain_transitivity_write(
    log: BarrierLog,
    state: SyncState,
    dst_stage: nat,
    dst_access: nat,
    i: nat,
    j: nat,
    mid_stage: nat,
    mid_access: nat,
)
    requires
        state.last_write.is_some() || state.last_reads.len() > 0,
        barrier_chain_write_2(log, state, dst_stage, dst_access, i, j, mid_stage, mid_access),
    ensures
        writable_chained(log, state, dst_stage, dst_access),
{
}

/// Appending a second barrier that continues from a first barrier's dst
/// creates a 2-barrier chain for reads.
pub proof fn lemma_append_chain_makes_readable(
    log: BarrierLog,
    state: SyncState,
    entry: BarrierEntry,
    first_idx: nat,
    mid_stage: nat,
    mid_access: nat,
    dst_stage: nat,
    dst_access: nat,
)
    requires
        state.last_write.is_some(),
        // First barrier in log covers write → mid
        first_idx < log.len(),
        resource_overlap(log[first_idx as int].resource, state.resource),
        stages_subset(state.write_stages, log[first_idx as int].src_stages),
        access_subset(state.write_accesses, log[first_idx as int].src_accesses),
        log[first_idx as int].dst_stages.stages.contains(mid_stage),
        log[first_idx as int].dst_accesses.accesses.contains(mid_access),
        // New entry covers mid → dst
        resource_overlap(entry.resource, state.resource),
        entry.src_stages.stages.contains(mid_stage),
        entry.src_accesses.accesses.contains(mid_access),
        entry.dst_stages.stages.contains(dst_stage),
        entry.dst_accesses.accesses.contains(dst_access),
    ensures
        readable_chained(log.push(entry), state, dst_stage, dst_access),
{
    let new_log = log.push(entry);
    let j: nat = log.len();
    assert(new_log[first_idx as int] == log[first_idx as int]);
    assert(new_log[j as int] == entry);
    assert(barrier_chain_read_2(new_log, state, dst_stage, dst_access, first_idx, j, mid_stage, mid_access));
}

} // verus!
