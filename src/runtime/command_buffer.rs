use vstd::prelude::*;
use crate::recording::*;
use crate::resource::*;
use crate::flags::*;
use crate::sync::*;

verus! {

/// Recording state of a command buffer.
pub enum CommandBufferStatus {
    /// Initial or reset state.
    Initial,
    /// Between begin and end.
    Recording,
    /// Recorded, ready for submission.
    Executable,
}

/// Runtime wrapper for a Vulkan command buffer.
pub struct RuntimeCommandBuffer {
    /// Opaque handle (maps to VkCommandBuffer).
    pub handle: u64,
    /// Current status.
    pub status: Ghost<CommandBufferStatus>,
    /// Recorded barrier log (ghost).
    pub barrier_log: Ghost<BarrierLog>,
    /// Whether we are inside a render pass.
    pub in_render_pass: Ghost<bool>,
}

/// Well-formedness of the runtime command buffer.
pub open spec fn runtime_cb_wf(cb: &RuntimeCommandBuffer) -> bool {
    true
}

/// Command buffer is in recording state.
pub open spec fn is_recording(cb: &RuntimeCommandBuffer) -> bool {
    match cb.status@ {
        CommandBufferStatus::Recording => true,
        _ => false,
    }
}

/// Command buffer is executable.
pub open spec fn is_executable(cb: &RuntimeCommandBuffer) -> bool {
    match cb.status@ {
        CommandBufferStatus::Executable => true,
        _ => false,
    }
}

/// Exec: begin recording.
pub fn begin_recording_exec(cb: &mut RuntimeCommandBuffer)
    requires
        match old(cb).status@ {
            CommandBufferStatus::Initial => true,
            _ => false,
        },
    ensures
        is_recording(cb),
        cb.barrier_log@ == Seq::<BarrierEntry>::empty(),
        cb.in_render_pass@ == false,
{
    cb.status = Ghost(CommandBufferStatus::Recording);
    cb.barrier_log = Ghost(Seq::empty());
    cb.in_render_pass = Ghost(false);
}

/// Exec: end recording.
pub fn end_recording_exec(cb: &mut RuntimeCommandBuffer)
    requires
        is_recording(&*old(cb)),
        old(cb).in_render_pass@ == false,
    ensures
        is_executable(cb),
{
    cb.status = Ghost(CommandBufferStatus::Executable);
}

/// Exec: begin render pass.
pub fn cmd_begin_render_pass_exec(cb: &mut RuntimeCommandBuffer)
    requires
        is_recording(&*old(cb)),
        old(cb).in_render_pass@ == false,
    ensures
        is_recording(cb),
        cb.in_render_pass@ == true,
{
    cb.in_render_pass = Ghost(true);
}

/// Exec: end render pass.
pub fn cmd_end_render_pass_exec(cb: &mut RuntimeCommandBuffer)
    requires
        is_recording(&*old(cb)),
        old(cb).in_render_pass@ == true,
    ensures
        is_recording(cb),
        cb.in_render_pass@ == false,
{
    cb.in_render_pass = Ghost(false);
}

/// Exec: record a pipeline barrier.
pub fn cmd_pipeline_barrier_exec(
    cb: &mut RuntimeCommandBuffer,
    entry: Ghost<BarrierEntry>,
)
    requires
        is_recording(&*old(cb)),
    ensures
        is_recording(cb),
        cb.barrier_log@ == old(cb).barrier_log@.push(entry@),
{
    cb.barrier_log = Ghost(cb.barrier_log@.push(entry@));
}

/// Exec: bind a pipeline (ghost no-op on barrier log).
pub fn cmd_bind_pipeline_exec(cb: &mut RuntimeCommandBuffer, pipeline_id: Ghost<nat>)
    requires
        is_recording(&*old(cb)),
    ensures
        is_recording(cb),
        cb.barrier_log@ == old(cb).barrier_log@,
{
}

/// Exec: record a draw command (ghost no-op on barrier log).
pub fn cmd_draw_exec(cb: &mut RuntimeCommandBuffer)
    requires
        is_recording(&*old(cb)),
        old(cb).in_render_pass@ == true,
    ensures
        is_recording(cb),
        cb.barrier_log@ == old(cb).barrier_log@,
{
}

/// Exec: record a dispatch command (ghost no-op on barrier log).
pub fn cmd_dispatch_exec(cb: &mut RuntimeCommandBuffer)
    requires
        is_recording(&*old(cb)),
        old(cb).in_render_pass@ == false,
    ensures
        is_recording(cb),
        cb.barrier_log@ == old(cb).barrier_log@,
{
}

// ── Extended Specs & Proofs ──────────────────────────────────────────

/// Command buffer is in initial state.
pub open spec fn is_initial(cb: &RuntimeCommandBuffer) -> bool {
    match cb.status@ {
        CommandBufferStatus::Initial => true,
        _ => false,
    }
}

/// Number of barriers recorded so far.
pub open spec fn barrier_count(cb: &RuntimeCommandBuffer) -> nat {
    cb.barrier_log@.len()
}

/// Command buffer has no recorded barriers.
pub open spec fn has_no_barriers(cb: &RuntimeCommandBuffer) -> bool {
    cb.barrier_log@.len() == 0
}

/// Proof: begin recording from initial produces recording state.
pub proof fn lemma_begin_produces_recording(cb: &RuntimeCommandBuffer)
    requires is_initial(cb),
    ensures ({
        let new_cb = RuntimeCommandBuffer {
            handle: cb.handle,
            status: Ghost(CommandBufferStatus::Recording),
            barrier_log: Ghost(Seq::empty()),
            in_render_pass: Ghost(false),
        };
        is_recording(&new_cb)
    }),
{
}

/// Proof: end recording from recording produces executable.
pub proof fn lemma_end_produces_executable(cb: &RuntimeCommandBuffer)
    requires
        is_recording(cb),
        cb.in_render_pass@ == false,
    ensures ({
        let new_cb = RuntimeCommandBuffer {
            handle: cb.handle,
            status: Ghost(CommandBufferStatus::Executable),
            barrier_log: cb.barrier_log,
            in_render_pass: cb.in_render_pass,
        };
        is_executable(&new_cb)
    }),
{
}

/// Proof: recording a barrier increments the count by 1.
pub proof fn lemma_barrier_increments_count(
    cb: &RuntimeCommandBuffer,
    entry: Ghost<BarrierEntry>,
)
    requires is_recording(cb),
    ensures cb.barrier_log@.push(entry@).len() == cb.barrier_log@.len() + 1,
{
}

/// Proof: a fresh recording has no barriers.
pub proof fn lemma_fresh_recording_no_barriers()
    ensures Seq::<BarrierEntry>::empty().len() == 0,
{
}

/// Proof: initial is not recording.
pub proof fn lemma_initial_not_recording(cb: &RuntimeCommandBuffer)
    requires is_initial(cb),
    ensures !is_recording(cb),
{
}

/// Proof: initial is not executable.
pub proof fn lemma_initial_not_executable(cb: &RuntimeCommandBuffer)
    requires is_initial(cb),
    ensures !is_executable(cb),
{
}

/// Proof: recording is not executable.
pub proof fn lemma_recording_not_executable(cb: &RuntimeCommandBuffer)
    requires is_recording(cb),
    ensures !is_executable(cb),
{
}

/// Proof: executable is not recording.
pub proof fn lemma_executable_not_recording(cb: &RuntimeCommandBuffer)
    requires is_executable(cb),
    ensures !is_recording(cb),
{
}

} // verus!
