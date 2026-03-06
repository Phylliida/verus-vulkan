use vstd::prelude::*;

verus! {

/// Lifecycle state of a command buffer, mirroring the Vulkan spec.
pub enum CommandBufferState {
    /// Allocated but not yet begun recording.
    Initial,
    /// Between vkBeginCommandBuffer and vkEndCommandBuffer.
    Recording,
    /// Recording finished; ready for submission.
    Executable,
    /// Submitted to a queue; pending execution.
    Pending,
    /// Entered an invalid state (e.g., after a failed recording).
    Invalid,
}

/// Transition from Initial to Recording (vkBeginCommandBuffer).
pub open spec fn begin_recording(state: CommandBufferState) -> Option<CommandBufferState> {
    match state {
        CommandBufferState::Initial => Some(CommandBufferState::Recording),
        // One-time-submit or reset-before-rerecord:
        CommandBufferState::Executable => Some(CommandBufferState::Recording),
        _ => None,
    }
}

/// Transition from Recording to Executable (vkEndCommandBuffer).
pub open spec fn end_recording(state: CommandBufferState) -> Option<CommandBufferState> {
    match state {
        CommandBufferState::Recording => Some(CommandBufferState::Executable),
        _ => None,
    }
}

/// Transition from Executable to Pending (vkQueueSubmit).
pub open spec fn submit(state: CommandBufferState) -> Option<CommandBufferState> {
    match state {
        CommandBufferState::Executable => Some(CommandBufferState::Pending),
        _ => None,
    }
}

/// Transition from Pending back to Executable (fence signaled).
pub open spec fn complete_execution(state: CommandBufferState) -> Option<CommandBufferState> {
    match state {
        CommandBufferState::Pending => Some(CommandBufferState::Executable),
        _ => None,
    }
}

/// Reset to Initial (vkResetCommandBuffer).
pub open spec fn reset(state: CommandBufferState) -> Option<CommandBufferState> {
    match state {
        CommandBufferState::Recording => Some(CommandBufferState::Initial),
        CommandBufferState::Executable => Some(CommandBufferState::Initial),
        CommandBufferState::Invalid => Some(CommandBufferState::Initial),
        _ => None,
    }
}

/// The recording-submit-complete cycle returns to Executable.
pub proof fn lemma_record_submit_complete_cycle()
    ensures ({
        let s0 = CommandBufferState::Initial;
        let s1 = begin_recording(s0);
        let s2 = match s1 { Some(s) => end_recording(s), None => None };
        let s3 = match s2 { Some(s) => submit(s), None => None };
        let s4 = match s3 { Some(s) => complete_execution(s), None => None };
        s4 == Some(CommandBufferState::Executable)
    }),
{
}

/// Reset from any non-Initial/non-Pending state produces Initial.
pub proof fn lemma_reset_produces_initial(state: CommandBufferState)
    requires
        state != CommandBufferState::Initial,
        state != CommandBufferState::Pending,
    ensures
        reset(state) == Some(CommandBufferState::Initial),
{
}

} // verus!
