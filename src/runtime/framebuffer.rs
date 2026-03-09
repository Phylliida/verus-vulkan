use vstd::prelude::*;
use crate::framebuffer::*;
use crate::lifetime::*;
use crate::render_pass::*;
use crate::sync_token::*;
use super::device::RuntimeDevice;

verus! {

// ── Image View Runtime ─────────────────────────────────────────────────

/// Runtime wrapper for a Vulkan image view.
pub struct RuntimeImageView {
    /// Opaque handle (maps to VkImageView).
    pub handle: u64,
    /// Ghost model of the image view state.
    pub state: Ghost<ImageViewState>,
}

impl View for RuntimeImageView {
    type V = ImageViewState;
    open spec fn view(&self) -> ImageViewState { self.state@ }
}

/// Well-formedness of the runtime image view.
pub open spec fn runtime_image_view_wf(view: &RuntimeImageView) -> bool {
    image_view_well_formed(view@)
}

/// Exec: create an image view.
pub fn create_image_view_exec(
    ivs: Ghost<ImageViewState>,
) -> (out: RuntimeImageView)
    requires ivs@.alive,
    ensures
        out@ == ivs@,
        runtime_image_view_wf(&out),
{
    RuntimeImageView {
        handle: 0,
        state: ivs,
    }
}

/// Exec: destroy an image view.
/// Caller must prove exclusive access.
pub fn destroy_image_view_exec(
    view: &mut RuntimeImageView,
    dev: &RuntimeDevice,
    thread: Ghost<ThreadId>,
    reg: Ghost<TokenRegistry>,
)
    requires
        runtime_image_view_wf(&*old(view)),
        // All pending submissions must be completed
        forall|i: int| 0 <= i < dev@.pending_submissions.len()
            ==> (#[trigger] dev@.pending_submissions[i]).completed,
        holds_exclusive(reg@, old(view)@.id, thread@),
    ensures
        view@ == destroy_image_view_ghost(old(view)@),
        !view@.alive,
{
    view.state = Ghost(destroy_image_view_ghost(view.state@));
}

// ── Framebuffer Runtime ────────────────────────────────────────────────

/// Runtime wrapper for a Vulkan framebuffer.
pub struct RuntimeFramebuffer {
    /// Opaque handle (maps to VkFramebuffer).
    pub handle: u64,
    /// Ghost model of the framebuffer state.
    pub state: Ghost<FramebufferState>,
}

impl View for RuntimeFramebuffer {
    type V = FramebufferState;
    open spec fn view(&self) -> FramebufferState { self.state@ }
}

/// Well-formedness of the runtime framebuffer (alive).
pub open spec fn runtime_framebuffer_wf(fb: &RuntimeFramebuffer) -> bool {
    fb@.alive
}

/// Exec: create a framebuffer.
pub fn create_framebuffer_exec(
    fbs: Ghost<FramebufferState>,
) -> (out: RuntimeFramebuffer)
    requires fbs@.alive,
    ensures
        out@ == fbs@,
        runtime_framebuffer_wf(&out),
{
    RuntimeFramebuffer {
        handle: 0,
        state: fbs,
    }
}

/// Exec: destroy a framebuffer.
/// Caller must prove exclusive access.
pub fn destroy_framebuffer_exec(
    fb: &mut RuntimeFramebuffer,
    dev: &RuntimeDevice,
    thread: Ghost<ThreadId>,
    reg: Ghost<TokenRegistry>,
)
    requires
        runtime_framebuffer_wf(&*old(fb)),
        // All pending submissions must be completed
        forall|i: int| 0 <= i < dev@.pending_submissions.len()
            ==> (#[trigger] dev@.pending_submissions[i]).completed,
        holds_exclusive(reg@, old(fb)@.id, thread@),
    ensures
        fb@ == destroy_framebuffer_ghost(old(fb)@),
        !fb@.alive,
{
    fb.state = Ghost(destroy_framebuffer_ghost(fb.state@));
}

// ── Extended Specs & Proofs ──────────────────────────────────────────

/// Image view is alive.
pub open spec fn image_view_alive(view: &RuntimeImageView) -> bool {
    view@.alive
}

/// Framebuffer is alive.
pub open spec fn framebuffer_alive(fb: &RuntimeFramebuffer) -> bool {
    fb@.alive
}

/// Proof: creating an image view produces an alive view.
pub proof fn lemma_create_image_view_alive(ivs: Ghost<ImageViewState>)
    requires ivs@.alive,
    ensures image_view_alive(&RuntimeImageView {
        handle: 0,
        state: ivs,
    }),
{
}

/// Proof: creating a framebuffer produces an alive framebuffer.
pub proof fn lemma_create_framebuffer_alive(fbs: Ghost<FramebufferState>)
    requires fbs@.alive,
    ensures framebuffer_alive(&RuntimeFramebuffer {
        handle: 0,
        state: fbs,
    }),
{
}

/// Proof: destroying an image view preserves its id.
pub proof fn lemma_destroy_image_view_preserves_id_rt(view: &RuntimeImageView)
    requires runtime_image_view_wf(view),
    ensures destroy_image_view_ghost(view@).id == view@.id,
{
}

/// Proof: destroying a framebuffer preserves its id.
pub proof fn lemma_destroy_framebuffer_preserves_id_rt(fb: &RuntimeFramebuffer)
    requires runtime_framebuffer_wf(fb),
    ensures destroy_framebuffer_ghost(fb@).id == fb@.id,
{
}

} // verus!
