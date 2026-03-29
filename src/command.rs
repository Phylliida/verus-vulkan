use vstd::prelude::*;
use crate::sync_token::*;

verus! {

///  Lifecycle state of a command buffer, mirroring the Vulkan spec.
pub enum CommandBufferState {
    ///  Allocated but not yet begun recording.
    Initial,
    ///  Between vkBeginCommandBuffer and vkEndCommandBuffer.
    Recording,
    ///  Recording finished; ready for submission.
    Executable,
    ///  Submitted to a queue; pending execution.
    Pending,
    ///  Entered an invalid state (e.g., after a failed recording).
    Invalid,
}

///  Transition from Initial to Recording (vkBeginCommandBuffer).
///
///  Requires exclusive access to the command buffer.
///  Per Vulkan spec: "commandBuffer is an externally synchronized parameter."
pub open spec fn begin_recording(
    state: CommandBufferState,
    cb_id: nat,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<CommandBufferState> {
    if !holds_exclusive(reg, SyncObjectId::Handle(cb_id), thread) {
        None
    } else {
        match state {
            CommandBufferState::Initial => Some(CommandBufferState::Recording),
            //  One-time-submit or reset-before-rerecord:
            CommandBufferState::Executable => Some(CommandBufferState::Recording),
            _ => None,
        }
    }
}

///  Transition from Recording to Executable (vkEndCommandBuffer).
///
///  Requires exclusive access to the command buffer.
pub open spec fn end_recording(
    state: CommandBufferState,
    cb_id: nat,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<CommandBufferState> {
    if !holds_exclusive(reg, SyncObjectId::Handle(cb_id), thread) {
        None
    } else {
        match state {
            CommandBufferState::Recording => Some(CommandBufferState::Executable),
            _ => None,
        }
    }
}

///  Transition from Executable to Pending (vkQueueSubmit).
///
///  Requires exclusive access to the queue (enforced by queue.rs).
///  The CB itself transitions without per-CB sync (the queue owns it now).
pub open spec fn submit(state: CommandBufferState) -> Option<CommandBufferState> {
    match state {
        CommandBufferState::Executable => Some(CommandBufferState::Pending),
        _ => None,
    }
}

///  Transition from Pending back to Executable (fence signaled).
pub open spec fn complete_execution(state: CommandBufferState) -> Option<CommandBufferState> {
    match state {
        CommandBufferState::Pending => Some(CommandBufferState::Executable),
        _ => None,
    }
}

///  Reset to Initial (vkResetCommandBuffer).
///
///  Requires exclusive access to the command buffer.
pub open spec fn reset(
    state: CommandBufferState,
    cb_id: nat,
    thread: ThreadId,
    reg: TokenRegistry,
) -> Option<CommandBufferState> {
    if !holds_exclusive(reg, SyncObjectId::Handle(cb_id), thread) {
        None
    } else {
        match state {
            CommandBufferState::Recording => Some(CommandBufferState::Initial),
            CommandBufferState::Executable => Some(CommandBufferState::Initial),
            CommandBufferState::Invalid => Some(CommandBufferState::Initial),
            _ => None,
        }
    }
}

///  The recording-submit-complete cycle returns to Executable.
pub proof fn lemma_record_submit_complete_cycle(
    cb_id: nat,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires holds_exclusive(reg, SyncObjectId::Handle(cb_id), thread),
    ensures ({
        let s0 = CommandBufferState::Initial;
        let s1 = begin_recording(s0, cb_id, thread, reg);
        let s2 = match s1 { Some(s) => end_recording(s, cb_id, thread, reg), None => None };
        let s3 = match s2 { Some(s) => submit(s), None => None };
        let s4 = match s3 { Some(s) => complete_execution(s), None => None };
        s4 == Some(CommandBufferState::Executable)
    }),
{
}

///  Reset from any non-Initial/non-Pending state produces Initial.
pub proof fn lemma_reset_produces_initial(
    state: CommandBufferState,
    cb_id: nat,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires
        state != CommandBufferState::Initial,
        state != CommandBufferState::Pending,
        holds_exclusive(reg, SyncObjectId::Handle(cb_id), thread),
    ensures
        reset(state, cb_id, thread, reg) == Some(CommandBufferState::Initial),
{
}

///  begin_recording requires exclusive access.
pub proof fn lemma_begin_requires_exclusive(
    state: CommandBufferState,
    cb_id: nat,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires begin_recording(state, cb_id, thread, reg).is_some(),
    ensures holds_exclusive(reg, SyncObjectId::Handle(cb_id), thread),
{
}

///  Without exclusive access, begin_recording fails.
pub proof fn lemma_no_exclusive_no_recording(
    state: CommandBufferState,
    cb_id: nat,
    thread: ThreadId,
    reg: TokenRegistry,
)
    requires !holds_exclusive(reg, SyncObjectId::Handle(cb_id), thread),
    ensures begin_recording(state, cb_id, thread, reg).is_none(),
{
}

} //  verus!
