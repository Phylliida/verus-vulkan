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
    /// Queue this submission was submitted to.
    pub queue_id: nat,
    /// Resources used by command buffers in this submission.
    pub referenced_resources: Set<ResourceId>,
    /// Fence to signal on completion (None if no fence).
    pub fence_id: Option<nat>,
    /// Whether the GPU has finished executing this submission.
    pub completed: bool,
    /// Command buffer ids submitted in this batch.
    pub command_buffers: Seq<nat>,
    /// Semaphore ids to signal when execution completes.
    pub signal_semaphores: Seq<nat>,
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

/// After mark_fence_completed + remove_completed, no remaining submission
/// has fence_id == Some(fence).
pub proof fn lemma_remove_completed_no_fence(
    submissions: Seq<SubmissionRecord>,
    fence: nat,
)
    ensures ({
        let marked = mark_fence_completed(submissions, fence);
        let cleaned = remove_completed(marked);
        forall|i: int| #![trigger cleaned[i]]
            0 <= i < cleaned.len()
            ==> cleaned[i].fence_id != Some(fence)
    }),
{
    let marked = mark_fence_completed(submissions, fence);
    // After marking, every entry with fence_id == Some(fence) has completed == true
    assert forall|i: int| #![trigger marked[i]]
        0 <= i < marked.len()
        implies (marked[i].fence_id == Some(fence) ==> marked[i].completed) by {
    }
    // remove_completed removes all completed entries, so survivors have fence_id != Some(fence)
    lemma_remove_completed_no_fence_helper(marked, fence);
}

/// Helper: if every entry with fence_id == Some(fence) is completed,
/// then remove_completed produces a seq with no such entries.
proof fn lemma_remove_completed_no_fence_helper(
    submissions: Seq<SubmissionRecord>,
    fence: nat,
)
    requires
        forall|i: int| #![trigger submissions[i]]
            0 <= i < submissions.len()
            ==> (submissions[i].fence_id == Some(fence) ==> submissions[i].completed),
    ensures ({
        let cleaned = remove_completed(submissions);
        forall|i: int| #![trigger cleaned[i]]
            0 <= i < cleaned.len()
            ==> cleaned[i].fence_id != Some(fence)
    }),
    decreases submissions.len(),
{
    if submissions.len() > 0 {
        let head = submissions[0];
        let tail = submissions.subrange(1, submissions.len() as int);

        // Establish precondition for recursive call
        assert forall|i: int| #![trigger tail[i]]
            0 <= i < tail.len()
            implies (tail[i].fence_id == Some(fence) ==> tail[i].completed) by {
            assert(tail[i] == submissions[i + 1]);
        }

        lemma_remove_completed_no_fence_helper(tail, fence);

        if head.completed {
            // Head removed; result == remove_completed(tail), done by IH
        } else {
            // Head kept and head.fence_id != Some(fence) (otherwise it'd be completed)
            let result = remove_completed(submissions);
            let tail_result = remove_completed(tail);
            assert forall|i: int| #![trigger result[i]]
                0 <= i < result.len()
                implies result[i].fence_id != Some(fence) by {
                if i == 0 {
                    assert(result[0] == head);
                } else {
                    assert(result[i] == tail_result[i - 1]);
                }
            }
        }
    }
}

// ── Wait-Idle Lemmas ────────────────────────────────────────────────────

/// After vkDeviceWaitIdle, no pending references remain (empty submissions).
pub proof fn lemma_device_wait_idle_clears_all(resource: ResourceId)
    ensures
        no_pending_references(Seq::<SubmissionRecord>::empty(), resource),
{
}

/// filter_by_queue preserves no_pending_references.
/// Mirrors lemma_remove_preserves_no_pending but filters by queue_id.
pub proof fn lemma_filter_preserves_no_pending(
    submissions: Seq<SubmissionRecord>,
    queue_id: nat,
    resource: ResourceId,
)
    requires
        no_pending_references(submissions, resource),
    ensures
        no_pending_references(
            crate::device::filter_by_queue(submissions, queue_id),
            resource,
        ),
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

        lemma_filter_preserves_no_pending(tail, queue_id, resource);

        if head.queue_id == queue_id {
            // Head filtered out; result == filter(tail), done by IH
        } else {
            // Head kept; result == [head] ++ filter(tail)
            let result = crate::device::filter_by_queue(submissions, queue_id);
            let tail_result = crate::device::filter_by_queue(tail, queue_id);
            assert forall|i: int| #![trigger result[i]]
                0 <= i < result.len()
                implies (result[i].completed || !result[i].referenced_resources.contains(resource)) by {
                if i == 0 {
                    assert(result[0] == head);
                    assert(head == submissions[0]);
                } else {
                    assert(result[i] == tail_result[i - 1]);
                }
            }
        }
    }
}

/// If all submissions referencing a resource are on queue_id,
/// then vkQueueWaitIdle on that queue clears the resource.
pub proof fn lemma_queue_wait_clears_queue_submissions(
    submissions: Seq<SubmissionRecord>,
    queue_id: nat,
    resource: ResourceId,
)
    requires
        // Every submission referencing this resource is on this queue
        forall|i: int| #![trigger submissions[i]]
            0 <= i < submissions.len()
            && submissions[i].referenced_resources.contains(resource)
            ==> submissions[i].queue_id == queue_id,
    ensures
        no_pending_references(
            crate::device::filter_by_queue(submissions, queue_id),
            resource,
        ),
    decreases submissions.len(),
{
    if submissions.len() > 0 {
        let head = submissions[0];
        let tail = submissions.subrange(1, submissions.len() as int);

        // Establish precondition for recursive call
        assert forall|i: int| #![trigger tail[i]]
            0 <= i < tail.len()
            && tail[i].referenced_resources.contains(resource)
            implies tail[i].queue_id == queue_id by {
            assert(tail[i] == submissions[i + 1]);
        }

        lemma_queue_wait_clears_queue_submissions(tail, queue_id, resource);

        if head.queue_id == queue_id {
            // Head is on this queue, filtered out
        } else {
            // Head is on another queue, kept — but it can't reference resource
            let result = crate::device::filter_by_queue(submissions, queue_id);
            let tail_result = crate::device::filter_by_queue(tail, queue_id);
            assert forall|i: int| #![trigger result[i]]
                0 <= i < result.len()
                implies (result[i].completed || !result[i].referenced_resources.contains(resource)) by {
                if i == 0 {
                    assert(result[0] == head);
                    assert(head == submissions[0]);
                    // head.queue_id != queue_id, so head can't reference resource
                } else {
                    assert(result[i] == tail_result[i - 1]);
                }
            }
        }
    }
}

} // verus!
