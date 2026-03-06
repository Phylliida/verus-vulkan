use vstd::prelude::*;
use crate::resource::*;

verus! {

/// A record of a single GPU submission (vkQueueSubmit).
///
/// Tracks which resources are referenced so the host can determine when
/// it is safe to destroy them. A fence may be associated for host-side
/// completion detection.
pub struct SubmissionRecord {
    /// Unique submission identifier.
    pub id: nat,
    /// Resources used by command buffers in this submission.
    pub referenced_resources: Set<ResourceId>,
    /// Fence to signal on completion (None if no fence).
    pub fence_id: Option<nat>,
    /// Whether the GPU has finished executing this submission.
    pub completed: bool,
}

/// True iff `resource` is not referenced by any pending (incomplete) submission.
pub open spec fn no_pending_references(
    submissions: Seq<SubmissionRecord>,
    resource: ResourceId,
) -> bool {
    forall|i: int| #![trigger submissions[i]]
        0 <= i < submissions.len()
        ==> (submissions[i].completed || !submissions[i].referenced_resources.contains(resource))
}

/// Mark all submissions with matching fence_id as completed.
/// Non-recursive: uses Seq::new for easy Z3 reasoning.
pub open spec fn mark_fence_completed(
    submissions: Seq<SubmissionRecord>,
    fence: nat,
) -> Seq<SubmissionRecord> {
    Seq::new(submissions.len(), |i: int|
        if submissions[i].fence_id == Some(fence) {
            SubmissionRecord { completed: true, ..submissions[i] }
        } else {
            submissions[i]
        }
    )
}

/// Remove all completed submissions from the log.
pub open spec fn remove_completed(
    submissions: Seq<SubmissionRecord>,
) -> Seq<SubmissionRecord>
    decreases submissions.len(),
{
    if submissions.len() == 0 {
        Seq::empty()
    } else {
        let head = submissions[0];
        let rest = remove_completed(submissions.subrange(1, submissions.len() as int));
        if head.completed {
            rest
        } else {
            Seq::new(1, |_i| head).add(rest)
        }
    }
}

// ── Lemmas ──────────────────────────────────────────────────────────────

/// After marking a fence completed and removing completed submissions,
/// no submission referencing `resource` remains pending.
pub proof fn lemma_wait_clears_fence_submissions(
    submissions: Seq<SubmissionRecord>,
    fence: nat,
    resource: ResourceId,
)
    requires
        // Every submission that references this resource has this fence_id
        forall|i: int| 0 <= i < submissions.len()
            && submissions[i].referenced_resources.contains(resource)
            ==> submissions[i].fence_id == Some(fence),
    ensures
        no_pending_references(
            remove_completed(mark_fence_completed(submissions, fence)),
            resource,
        ),
{
    // Step 1: after marking, no_pending_references holds on the marked seq
    let marked = mark_fence_completed(submissions, fence);
    assert forall|i: int| #![trigger marked[i]]
        0 <= i < marked.len()
        implies (marked[i].completed || !marked[i].referenced_resources.contains(resource)) by {
        // Seq::new gives us marked[i] directly
        if submissions[i].fence_id == Some(fence) {
            // marked[i].completed == true
        } else {
            // marked[i] == submissions[i]; if it referenced resource, fence_id would match
        }
    }
    // Step 2: remove_completed preserves the property
    lemma_remove_preserves_no_pending(marked, resource);
}

/// A freshly created resource (not in any submission) has no pending references.
pub proof fn lemma_fresh_resource_not_referenced(
    submissions: Seq<SubmissionRecord>,
    resource: ResourceId,
)
    requires
        forall|i: int| 0 <= i < submissions.len()
            ==> !submissions[i].referenced_resources.contains(resource),
    ensures
        no_pending_references(submissions, resource),
{
}

/// An empty submission log trivially has no pending references.
pub proof fn lemma_empty_submissions_no_references(resource: ResourceId)
    ensures no_pending_references(Seq::<SubmissionRecord>::empty(), resource),
{
}

/// Appending a submission that does NOT reference the resource preserves
/// the no_pending_references property.
pub proof fn lemma_submit_preserves_unreferenced(
    submissions: Seq<SubmissionRecord>,
    new_sub: SubmissionRecord,
    resource: ResourceId,
)
    requires
        no_pending_references(submissions, resource),
        !new_sub.referenced_resources.contains(resource),
    ensures
        no_pending_references(submissions.push(new_sub), resource),
{
    let extended = submissions.push(new_sub);
    assert forall|i: int| #![trigger extended[i]]
        0 <= i < extended.len()
        implies (extended[i].completed || !extended[i].referenced_resources.contains(resource)) by {
        if i < submissions.len() as int {
            assert(extended[i] == submissions[i]);
        } else {
            assert(extended[i] == new_sub);
        }
    }
}

/// Removing completed submissions never introduces new pending references.
pub proof fn lemma_remove_preserves_no_pending(
    submissions: Seq<SubmissionRecord>,
    resource: ResourceId,
)
    requires
        no_pending_references(submissions, resource),
    ensures
        no_pending_references(remove_completed(submissions), resource),
    decreases submissions.len(),
{
    if submissions.len() > 0 {
        let head = submissions[0];
        let tail = submissions.subrange(1, submissions.len() as int);

        // Establish precondition for recursive call
        assert forall|i: int| #![trigger tail[i]]
            0 <= i < tail.len()
            implies (tail[i].completed || !tail[i].referenced_resources.contains(resource)) by {
            assert(tail[i] == submissions[i + 1]);
        }

        lemma_remove_preserves_no_pending(tail, resource);

        if head.completed {
            // Head removed; result == remove_completed(tail), done by IH
        } else {
            // Head kept; result == [head] ++ remove_completed(tail)
            let result = remove_completed(submissions);
            let tail_result = remove_completed(tail);
            assert forall|i: int| #![trigger result[i]]
                0 <= i < result.len()
                implies (result[i].completed || !result[i].referenced_resources.contains(resource)) by {
                if i == 0 {
                    // result[0] == head; head is submissions[0]
                    assert(result[0] == head);
                    assert(head == submissions[0]);
                } else {
                    // result[i] is from tail_result
                    assert(result[i] == tail_result[i - 1]);
                }
            }
        }
    }
}

} // verus!
