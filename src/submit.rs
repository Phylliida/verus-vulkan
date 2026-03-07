use vstd::prelude::*;
use crate::command::*;
use crate::semaphore::*;

verus! {

// ── Helpers ─────────────────────────────────────────────────────────────

/// Whether `k` appears in the sequence `s`.
pub open spec fn seq_contains_nat(s: Seq<nat>, k: nat) -> bool
    decreases s.len(),
{
    if s.len() == 0 {
        false
    } else {
        s.last() == k || seq_contains_nat(s.subrange(0, s.len() - 1), k)
    }
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// Recursively transition each command buffer in `cbs` to Pending.
/// Processes from last to first: insert cbs.last() as Pending, then recurse on prefix.
pub open spec fn transition_cbs_to_pending(
    cbs: Seq<nat>,
    cb_states: Map<nat, CommandBufferState>,
) -> Map<nat, CommandBufferState>
    decreases cbs.len(),
{
    if cbs.len() == 0 {
        cb_states
    } else {
        let prefix_result = transition_cbs_to_pending(
            cbs.subrange(0, cbs.len() - 1),
            cb_states,
        );
        prefix_result.insert(cbs.last(), CommandBufferState::Pending)
    }
}

/// Recursively consume (wait on) each semaphore in `waits`.
/// Processes from last to first: call wait_semaphore_ghost on waits.last(), then recurse on prefix.
pub open spec fn consume_wait_semaphores(
    waits: Seq<nat>,
    sem_states: Map<nat, SemaphoreState>,
) -> Map<nat, SemaphoreState>
    decreases waits.len(),
{
    if waits.len() == 0 {
        sem_states
    } else {
        let prefix_result = consume_wait_semaphores(
            waits.subrange(0, waits.len() - 1),
            sem_states,
        );
        let old_sem = prefix_result[waits.last()];
        prefix_result.insert(waits.last(), wait_semaphore_ghost(old_sem))
    }
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// After transition_cbs_to_pending, every CB in the sequence is Pending.
pub proof fn lemma_transition_sets_pending(
    cbs: Seq<nat>,
    cb_states: Map<nat, CommandBufferState>,
    i: int,
)
    requires
        0 <= i < cbs.len(),
        // All CBs in the sequence are in the map
        forall|j: int| 0 <= j < cbs.len()
            ==> cb_states.contains_key(#[trigger] cbs[j]),
    ensures
        transition_cbs_to_pending(cbs, cb_states).contains_key(cbs[i])
        && transition_cbs_to_pending(cbs, cb_states)[cbs[i]] == CommandBufferState::Pending,
    decreases cbs.len(),
{
    if cbs.len() > 0 {
        let prefix = cbs.subrange(0, cbs.len() - 1);

        // Establish precondition for recursive call
        assert forall|j: int| 0 <= j < prefix.len()
            implies cb_states.contains_key(#[trigger] prefix[j]) by {
            assert(prefix[j] == cbs[j]);
        }

        if i == cbs.len() - 1 {
            // cbs[i] == cbs.last(), inserted last → in the result as Pending
        } else {
            // i < cbs.len() - 1, so cbs[i] == prefix[i]
            assert(cbs[i] == prefix[i]);
            lemma_transition_sets_pending(prefix, cb_states, i);

            let prefix_result = transition_cbs_to_pending(prefix, cb_states);
            // After inserting cbs.last(), prefix_result[cbs[i]] is preserved
            // unless cbs.last() == cbs[i], in which case it's still Pending
        }
    }
}

/// transition_cbs_to_pending preserves entries not in the sequence.
pub proof fn lemma_transition_preserves_others(
    cbs: Seq<nat>,
    cb_states: Map<nat, CommandBufferState>,
    k: nat,
)
    requires
        !seq_contains_nat(cbs, k),
        cb_states.contains_key(k),
    ensures
        transition_cbs_to_pending(cbs, cb_states).contains_key(k)
        && transition_cbs_to_pending(cbs, cb_states)[k] == cb_states[k],
    decreases cbs.len(),
{
    if cbs.len() > 0 {
        let prefix = cbs.subrange(0, cbs.len() - 1);

        // k != cbs.last() (since !seq_contains_nat(cbs, k))
        // !seq_contains_nat(prefix, k) (since seq_contains_nat unfolds to last || prefix)

        lemma_transition_preserves_others(prefix, cb_states, k);
        // prefix_result[k] == cb_states[k]
        // Inserting cbs.last() (which != k) preserves the entry
    }
}

/// After consume_wait_semaphores, every waited semaphore is unsignaled.
pub proof fn lemma_consume_unsignals_waits(
    waits: Seq<nat>,
    sem_states: Map<nat, SemaphoreState>,
    i: int,
)
    requires
        0 <= i < waits.len(),
        // All wait sems are in the map
        forall|j: int| 0 <= j < waits.len()
            ==> sem_states.contains_key(#[trigger] waits[j]),
    ensures
        consume_wait_semaphores(waits, sem_states).contains_key(waits[i])
        && !consume_wait_semaphores(waits, sem_states)[waits[i]].signaled,
    decreases waits.len(),
{
    if waits.len() > 0 {
        let prefix = waits.subrange(0, waits.len() - 1);

        assert forall|j: int| 0 <= j < prefix.len()
            implies sem_states.contains_key(#[trigger] prefix[j]) by {
            assert(prefix[j] == waits[j]);
        }

        if i == waits.len() - 1 {
            // waits[i] == waits.last(), waited on last → unsignaled
            let prefix_result = consume_wait_semaphores(prefix, sem_states);
            // Need to show prefix_result.contains_key(waits.last())
            if seq_contains_nat(prefix, waits.last()) {
                // It was processed in the prefix, so it's in prefix_result
                lemma_consume_contains_key(prefix, sem_states, waits.last());
            } else {
                // Not in prefix, so preserved from sem_states
                lemma_consume_preserves_others(prefix, sem_states, waits.last());
            }
        } else {
            assert(waits[i] == prefix[i]);
            lemma_consume_unsignals_waits(prefix, sem_states, i);

            let prefix_result = consume_wait_semaphores(prefix, sem_states);

            if waits.last() == waits[i] {
                // Overwritten by the last wait → still unsignaled
            } else {
                // Different key, preserved from prefix_result
            }
        }
    }
}

/// Helper: after consume_wait_semaphores, any key that was in the seq is in the result.
proof fn lemma_consume_contains_key(
    waits: Seq<nat>,
    sem_states: Map<nat, SemaphoreState>,
    k: nat,
)
    requires
        seq_contains_nat(waits, k),
        forall|j: int| 0 <= j < waits.len()
            ==> sem_states.contains_key(#[trigger] waits[j]),
    ensures
        consume_wait_semaphores(waits, sem_states).contains_key(k),
    decreases waits.len(),
{
    if waits.len() > 0 {
        let prefix = waits.subrange(0, waits.len() - 1);

        assert forall|j: int| 0 <= j < prefix.len()
            implies sem_states.contains_key(#[trigger] prefix[j]) by {
            assert(prefix[j] == waits[j]);
        }

        if waits.last() == k {
            // Inserted by this step
            let prefix_result = consume_wait_semaphores(prefix, sem_states);
            // Need prefix_result.contains_key(k) for the indexing in consume_wait_semaphores
            if seq_contains_nat(prefix, k) {
                lemma_consume_contains_key(prefix, sem_states, k);
            } else {
                lemma_consume_preserves_others(prefix, sem_states, k);
            }
        } else {
            // k is in prefix
            lemma_consume_contains_key(prefix, sem_states, k);
        }
    }
}

/// consume_wait_semaphores preserves entries not in the sequence.
pub proof fn lemma_consume_preserves_others(
    waits: Seq<nat>,
    sem_states: Map<nat, SemaphoreState>,
    k: nat,
)
    requires
        !seq_contains_nat(waits, k),
        sem_states.contains_key(k),
    ensures
        consume_wait_semaphores(waits, sem_states).contains_key(k)
        && consume_wait_semaphores(waits, sem_states)[k] == sem_states[k],
    decreases waits.len(),
{
    if waits.len() > 0 {
        let prefix = waits.subrange(0, waits.len() - 1);

        // k != waits.last() and !seq_contains_nat(prefix, k)
        lemma_consume_preserves_others(prefix, sem_states, k);
    }
}

} // verus!
