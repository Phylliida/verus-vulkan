use vstd::prelude::*;
use crate::lifetime::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// Represents the ordering of submissions within a single queue.
///
/// Vulkan guarantees that submissions to the same queue execute in
/// submission order. Submissions to different queues have no implicit
/// ordering (require explicit semaphore synchronization).
pub struct SubmissionOrderState {
    /// Queue id.
    pub queue_id: nat,
    /// Ordered sequence of submission ids.
    pub submission_ids: Seq<nat>,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// Submission a is ordered before submission b on the same queue.
pub open spec fn submission_ordered_before(
    state: SubmissionOrderState,
    sub_a: nat,
    sub_b: nat,
) -> bool {
    exists|i: int, j: int|
        0 <= i < j < state.submission_ids.len()
        && #[trigger] state.submission_ids[i] == sub_a
        && #[trigger] state.submission_ids[j] == sub_b
}

/// Append a new submission to the queue.
pub open spec fn append_submission(
    state: SubmissionOrderState,
    sub_id: nat,
) -> SubmissionOrderState {
    SubmissionOrderState {
        submission_ids: state.submission_ids.push(sub_id),
        ..state
    }
}

/// A submission is in the queue's history.
pub open spec fn submission_in_queue(
    state: SubmissionOrderState,
    sub_id: nat,
) -> bool {
    exists|i: int| 0 <= i < state.submission_ids.len()
        && (#[trigger] state.submission_ids[i]) == sub_id
}

/// All submissions in the queue are distinct.
pub open spec fn submissions_distinct(state: SubmissionOrderState) -> bool {
    forall|i: int, j: int|
        0 <= i < state.submission_ids.len()
        && 0 <= j < state.submission_ids.len()
        && i != j
        ==> (#[trigger] state.submission_ids[i])
            != (#[trigger] state.submission_ids[j])
}

/// Signal-before-wait ordering: on the same queue, a semaphore signal
/// must be submitted before the wait that consumes it.
pub open spec fn signal_before_wait(
    state: SubmissionOrderState,
    signal_sub: nat,
    wait_sub: nat,
) -> bool {
    submission_ordered_before(state, signal_sub, wait_sub)
}

/// Two submissions on the same queue have an implicit execution dependency.
pub open spec fn implicit_execution_dependency(
    state: SubmissionOrderState,
    earlier: nat,
    later: nat,
) -> bool {
    submission_ordered_before(state, earlier, later)
}

/// An empty queue.
pub open spec fn empty_queue(queue_id: nat) -> SubmissionOrderState {
    SubmissionOrderState {
        queue_id,
        submission_ids: Seq::empty(),
    }
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// After appending, the new submission is in the queue.
pub proof fn lemma_append_in_queue(
    state: SubmissionOrderState,
    sub_id: nat,
)
    ensures
        submission_in_queue(append_submission(state, sub_id), sub_id),
{
    let new_state = append_submission(state, sub_id);
    let i = (new_state.submission_ids.len() - 1) as int;
    assert(new_state.submission_ids[i] == sub_id);
}

/// After appending, existing submissions are still in the queue.
pub proof fn lemma_append_preserves_membership(
    state: SubmissionOrderState,
    sub_id: nat,
    existing: nat,
)
    requires submission_in_queue(state, existing),
    ensures submission_in_queue(append_submission(state, sub_id), existing),
{
    let i = choose|i: int| 0 <= i < state.submission_ids.len()
        && (#[trigger] state.submission_ids[i]) == existing;
    let new_state = append_submission(state, sub_id);
    assert(new_state.submission_ids[i] == existing);
}

/// After appending, all previously submitted work is ordered before the new one.
pub proof fn lemma_append_ordered_before(
    state: SubmissionOrderState,
    sub_id: nat,
    existing: nat,
)
    requires submission_in_queue(state, existing),
    ensures
        submission_ordered_before(
            append_submission(state, sub_id),
            existing,
            sub_id,
        ),
{
    let i = choose|i: int| 0 <= i < state.submission_ids.len()
        && (#[trigger] state.submission_ids[i]) == existing;
    let new_state = append_submission(state, sub_id);
    let j = (new_state.submission_ids.len() - 1) as int;
    assert(new_state.submission_ids[i] == existing);
    assert(new_state.submission_ids[j] == sub_id);
}

/// Ordering is transitive.
pub proof fn lemma_ordering_transitive(
    state: SubmissionOrderState,
    a: nat,
    b: nat,
    c: nat,
)
    requires
        submissions_distinct(state),
        submission_ordered_before(state, a, b),
        submission_ordered_before(state, b, c),
    ensures
        submission_ordered_before(state, a, c),
{
    let ia = choose|i: int| exists|j: int|
        0 <= i < j < state.submission_ids.len()
        && #[trigger] state.submission_ids[i] == a
        && state.submission_ids[j] == b;
    let jb = choose|j: int|
        0 <= ia < j < state.submission_ids.len()
        && state.submission_ids[ia] == a
        && #[trigger] state.submission_ids[j] == b;
    let ib2 = choose|i: int| exists|j: int|
        0 <= i < j < state.submission_ids.len()
        && #[trigger] state.submission_ids[i] == b
        && state.submission_ids[j] == c;
    let jc = choose|j: int|
        0 <= ib2 < j < state.submission_ids.len()
        && state.submission_ids[ib2] == b
        && #[trigger] state.submission_ids[j] == c;
    // Since submissions are distinct, jb == ib2 (both have value b)
    // and ia < jb <= ib2 < jc, so ia < jc
    assert(state.submission_ids[ia] == a);
    assert(state.submission_ids[jc] == c);
}

/// An empty queue has no submissions.
pub proof fn lemma_empty_queue_no_submissions(queue_id: nat, sub: nat)
    ensures !submission_in_queue(empty_queue(queue_id), sub),
{
}

} // verus!
