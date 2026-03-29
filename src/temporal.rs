use vstd::prelude::*;
use crate::device::*;
use crate::resource::*;
use crate::lifetime::*;

verus! {

//  ── Spec Functions ──────────────────────────────────────────────────────

///  A resource budget: upper bounds on live resource counts.
pub struct ResourceBudget {
    pub max_buffers: nat,
    pub max_images: nat,
    pub max_pipelines: nat,
    pub max_descriptor_pools: nat,
    pub max_pending_submissions: nat,
}

///  The device is within budget.
pub open spec fn within_budget(dev: DeviceState, budget: ResourceBudget) -> bool {
    dev.live_buffers <= budget.max_buffers
    && dev.live_images <= budget.max_images
    && dev.live_pipelines <= budget.max_pipelines
    && dev.live_descriptor_pools <= budget.max_descriptor_pools
    && dev.pending_submissions.len() <= budget.max_pending_submissions
}

///  A single frame iteration: create some resources, destroy same number.
///  Models a frame that creates `n_bufs` transient buffers and `n_imgs`
///  transient images, uses them, and destroys them before the frame ends.
pub open spec fn balanced_frame_buffers(dev: DeviceState, n: nat) -> DeviceState {
    balanced_destroys_buffers(balanced_creates_buffers(dev, n), n)
}

///  Create n buffers.
pub open spec fn balanced_creates_buffers(dev: DeviceState, n: nat) -> DeviceState
    decreases n,
{
    if n == 0 {
        dev
    } else {
        create_buffer_ghost(balanced_creates_buffers(dev, (n - 1) as nat))
    }
}

///  Destroy n buffers.
pub open spec fn balanced_destroys_buffers(dev: DeviceState, n: nat) -> DeviceState
    recommends dev.live_buffers >= n,
    decreases n,
{
    if n == 0 {
        dev
    } else {
        destroy_buffer_ghost(balanced_destroys_buffers(dev, (n - 1) as nat))
    }
}

///  A submission lifecycle: add a submission, then retire it (via completion).
pub open spec fn submit_and_retire(
    dev: DeviceState,
    record: SubmissionRecord,
) -> DeviceState {
    retire_submission(submit_ghost_dev(dev, record))
}

///  Ghost submit: append a submission record.
pub open spec fn submit_ghost_dev(
    dev: DeviceState,
    record: SubmissionRecord,
) -> DeviceState {
    DeviceState {
        pending_submissions: dev.pending_submissions.push(record),
        ..dev
    }
}

///  Ghost retire: remove the oldest submission (FIFO).
pub open spec fn retire_submission(dev: DeviceState) -> DeviceState
    recommends dev.pending_submissions.len() > 0,
{
    DeviceState {
        pending_submissions: dev.pending_submissions.subrange(1, dev.pending_submissions.len() as int),
        ..dev
    }
}

//  ── Proofs ──────────────────────────────────────────────────────────────

///  N balanced creates increase live_buffers by n.
pub proof fn lemma_balanced_creates_count(dev: DeviceState, n: nat)
    ensures
        balanced_creates_buffers(dev, n).live_buffers == dev.live_buffers + n,
    decreases n,
{
    if n > 0 {
        lemma_balanced_creates_count(dev, (n - 1) as nat);
    }
}

///  N balanced destroys decrease live_buffers by n.
pub proof fn lemma_balanced_destroys_count(dev: DeviceState, n: nat)
    requires dev.live_buffers >= n,
    ensures
        balanced_destroys_buffers(dev, n).live_buffers == dev.live_buffers - n,
    decreases n,
{
    if n > 0 {
        lemma_balanced_destroys_count(dev, (n - 1) as nat);
        let prev = balanced_destroys_buffers(dev, (n - 1) as nat);
        assert(prev.live_buffers == dev.live_buffers - (n - 1));
        assert(prev.live_buffers >= 1);
    }
}

///  A balanced frame (create n, then destroy n) preserves the live buffer count.
pub proof fn lemma_balanced_frame_preserves_buffers(dev: DeviceState, n: nat)
    ensures
        balanced_frame_buffers(dev, n).live_buffers == dev.live_buffers,
{
    lemma_balanced_creates_count(dev, n);
    let after_creates = balanced_creates_buffers(dev, n);
    assert(after_creates.live_buffers == dev.live_buffers + n);
    lemma_balanced_destroys_count(after_creates, n);
}

///  A balanced frame preserves within_budget for the buffer count.
pub proof fn lemma_balanced_frame_within_budget(
    dev: DeviceState,
    budget: ResourceBudget,
    n: nat,
)
    requires
        within_budget(dev, budget),
    ensures
        balanced_frame_buffers(dev, n).live_buffers <= budget.max_buffers,
{
    lemma_balanced_frame_preserves_buffers(dev, n);
}

///  Submit then retire preserves pending_submissions length.
pub proof fn lemma_submit_retire_preserves_length(
    dev: DeviceState,
    record: SubmissionRecord,
)
    requires dev.pending_submissions.len() > 0,
    ensures
        submit_and_retire(dev, record).pending_submissions.len()
            == dev.pending_submissions.len(),
{
    let after_submit = submit_ghost_dev(dev, record);
    assert(after_submit.pending_submissions.len() == dev.pending_submissions.len() + 1);
    let after_retire = retire_submission(after_submit);
    assert(after_retire.pending_submissions.len() == after_submit.pending_submissions.len() - 1);
}

///  Submit then retire on empty starts at 0, goes to 1, can't retire (need non-empty).
///  Instead: submit-only increases length by 1.
pub proof fn lemma_submit_increases_pending(
    dev: DeviceState,
    record: SubmissionRecord,
)
    ensures
        submit_ghost_dev(dev, record).pending_submissions.len()
            == dev.pending_submissions.len() + 1,
{
}

///  Retire decreases pending submissions by 1.
pub proof fn lemma_retire_decreases_pending(dev: DeviceState)
    requires dev.pending_submissions.len() > 0,
    ensures
        retire_submission(dev).pending_submissions.len()
            == dev.pending_submissions.len() - 1,
{
}

///  Creating buffers does not affect pending submissions.
pub proof fn lemma_create_buffer_preserves_pending(dev: DeviceState)
    ensures
        create_buffer_ghost(dev).pending_submissions == dev.pending_submissions,
{
}

///  Destroying buffers does not affect pending submissions.
pub proof fn lemma_destroy_buffer_preserves_pending(dev: DeviceState)
    ensures
        destroy_buffer_ghost(dev).pending_submissions == dev.pending_submissions,
{
}

///  A balanced frame does not affect pending submissions.
pub proof fn lemma_balanced_frame_preserves_pending(dev: DeviceState, n: nat)
    ensures
        balanced_frame_buffers(dev, n).pending_submissions == dev.pending_submissions,
{
    lemma_balanced_creates_preserves_pending(dev, n);
    let after_creates = balanced_creates_buffers(dev, n);
    lemma_balanced_destroys_preserves_pending(after_creates, n);
}

///  N creates preserve pending submissions.
proof fn lemma_balanced_creates_preserves_pending(dev: DeviceState, n: nat)
    ensures
        balanced_creates_buffers(dev, n).pending_submissions == dev.pending_submissions,
    decreases n,
{
    if n > 0 {
        lemma_balanced_creates_preserves_pending(dev, (n - 1) as nat);
    }
}

///  N destroys preserve pending submissions.
proof fn lemma_balanced_destroys_preserves_pending(dev: DeviceState, n: nat)
    ensures
        balanced_destroys_buffers(dev, n).pending_submissions == dev.pending_submissions,
    decreases n,
{
    if n > 0 {
        lemma_balanced_destroys_preserves_pending(dev, (n - 1) as nat);
    }
}

///  Creating buffers does not affect images, pipelines, or descriptor pools.
pub proof fn lemma_balanced_creates_no_cross_effect(dev: DeviceState, n: nat)
    ensures
        balanced_creates_buffers(dev, n).live_images == dev.live_images,
        balanced_creates_buffers(dev, n).live_pipelines == dev.live_pipelines,
        balanced_creates_buffers(dev, n).live_descriptor_pools == dev.live_descriptor_pools,
    decreases n,
{
    if n > 0 {
        lemma_balanced_creates_no_cross_effect(dev, (n - 1) as nat);
    }
}

///  Destroying buffers does not affect images, pipelines, or descriptor pools.
pub proof fn lemma_balanced_destroys_no_cross_effect(dev: DeviceState, n: nat)
    ensures
        balanced_destroys_buffers(dev, n).live_images == dev.live_images,
        balanced_destroys_buffers(dev, n).live_pipelines == dev.live_pipelines,
        balanced_destroys_buffers(dev, n).live_descriptor_pools == dev.live_descriptor_pools,
    decreases n,
{
    if n > 0 {
        lemma_balanced_destroys_no_cross_effect(dev, (n - 1) as nat);
    }
}

///  A balanced frame preserves all non-buffer resource counts.
pub proof fn lemma_balanced_frame_preserves_other_resources(dev: DeviceState, n: nat)
    ensures
        balanced_frame_buffers(dev, n).live_images == dev.live_images,
        balanced_frame_buffers(dev, n).live_pipelines == dev.live_pipelines,
        balanced_frame_buffers(dev, n).live_descriptor_pools == dev.live_descriptor_pools,
{
    lemma_balanced_creates_no_cross_effect(dev, n);
    let after_creates = balanced_creates_buffers(dev, n);
    lemma_balanced_destroys_no_cross_effect(after_creates, n);
}

///  The main temporal invariant: a balanced frame preserves within_budget entirely.
pub proof fn lemma_balanced_frame_full_budget_invariant(
    dev: DeviceState,
    budget: ResourceBudget,
    n: nat,
)
    requires
        within_budget(dev, budget),
    ensures
        within_budget(
            balanced_frame_buffers(dev, n),
            ResourceBudget { max_pending_submissions: budget.max_pending_submissions, ..budget },
        ),
{
    lemma_balanced_frame_preserves_buffers(dev, n);
    lemma_balanced_frame_preserves_other_resources(dev, n);
    lemma_balanced_frame_preserves_pending(dev, n);
}

} //  verus!
