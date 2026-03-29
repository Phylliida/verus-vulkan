use vstd::prelude::*;

verus! {

//  ── Types ───────────────────────────────────────────────────────────────

///  Capabilities of a queue family.
pub struct QueueFamilyCapabilities {
    ///  Queue family index.
    pub family_index: nat,
    ///  Supports graphics operations.
    pub graphics: bool,
    ///  Supports compute operations.
    pub compute: bool,
    ///  Supports transfer operations.
    pub transfer: bool,
    ///  Supports sparse binding operations.
    pub sparse_binding: bool,
    ///  Number of queues in this family.
    pub queue_count: nat,
}

//  ── Spec Functions ──────────────────────────────────────────────────────

///  A queue family supports a graphics operation.
pub open spec fn supports_graphics(caps: QueueFamilyCapabilities) -> bool {
    caps.graphics
}

///  A queue family supports a compute operation.
pub open spec fn supports_compute(caps: QueueFamilyCapabilities) -> bool {
    caps.compute
}

///  A queue family supports a transfer operation.
pub open spec fn supports_transfer(caps: QueueFamilyCapabilities) -> bool {
    //  Graphics and compute queues implicitly support transfer
    caps.transfer || caps.graphics || caps.compute
}

///  A queue family supports sparse binding.
pub open spec fn supports_sparse(caps: QueueFamilyCapabilities) -> bool {
    caps.sparse_binding
}

///  A draw command requires a graphics-capable queue.
pub open spec fn draw_requires_graphics(caps: QueueFamilyCapabilities) -> bool {
    caps.graphics
}

///  A dispatch command requires a compute-capable queue.
pub open spec fn dispatch_requires_compute(caps: QueueFamilyCapabilities) -> bool {
    caps.compute
}

///  A transfer command requires a transfer-capable queue.
pub open spec fn transfer_requires_transfer(caps: QueueFamilyCapabilities) -> bool {
    supports_transfer(caps)
}

///  A command buffer submitted to a queue is compatible with the queue's capabilities.
pub open spec fn submission_compatible(
    caps: QueueFamilyCapabilities,
    uses_graphics: bool,
    uses_compute: bool,
    uses_transfer: bool,
) -> bool {
    (uses_graphics ==> caps.graphics)
    && (uses_compute ==> caps.compute)
    && (uses_transfer ==> supports_transfer(caps))
}

///  Queue family has available queues.
pub open spec fn has_available_queues(caps: QueueFamilyCapabilities) -> bool {
    caps.queue_count > 0
}

///  A dedicated compute queue (compute but not graphics).
pub open spec fn is_dedicated_compute(caps: QueueFamilyCapabilities) -> bool {
    caps.compute && !caps.graphics
}

///  A dedicated transfer queue (transfer but not graphics/compute).
pub open spec fn is_dedicated_transfer(caps: QueueFamilyCapabilities) -> bool {
    caps.transfer && !caps.graphics && !caps.compute
}

//  ── Proofs ──────────────────────────────────────────────────────────────

///  A graphics queue supports transfer.
pub proof fn lemma_graphics_supports_transfer(caps: QueueFamilyCapabilities)
    requires caps.graphics,
    ensures supports_transfer(caps),
{
}

///  A compute queue supports transfer.
pub proof fn lemma_compute_supports_transfer(caps: QueueFamilyCapabilities)
    requires caps.compute,
    ensures supports_transfer(caps),
{
}

///  A graphics+compute queue supports all operation types.
pub proof fn lemma_universal_queue(caps: QueueFamilyCapabilities)
    requires caps.graphics, caps.compute,
    ensures
        submission_compatible(caps, true, true, true),
{
}

///  A dedicated compute queue cannot run graphics commands.
pub proof fn lemma_dedicated_compute_no_graphics(caps: QueueFamilyCapabilities)
    requires is_dedicated_compute(caps),
    ensures !submission_compatible(caps, true, false, false),
{
}

///  A dedicated transfer queue can only run transfer commands.
pub proof fn lemma_dedicated_transfer_only(caps: QueueFamilyCapabilities)
    requires is_dedicated_transfer(caps),
    ensures
        submission_compatible(caps, false, false, true),
        !submission_compatible(caps, true, false, false),
        !submission_compatible(caps, false, true, false),
{
}

///  An empty submission is compatible with any queue.
pub proof fn lemma_empty_submission_any_queue(caps: QueueFamilyCapabilities)
    ensures submission_compatible(caps, false, false, false),
{
}

} //  verus!
