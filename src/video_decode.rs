use vstd::prelude::*;
use crate::resource::*;
use crate::image_layout::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// Video codec type (VK_KHR_video_decode_queue).
pub enum VideoCodecType {
    H264,
    H265,
    AV1,
    VP9,
}

/// Profile describing a video decode session.
pub struct VideoProfileState {
    pub codec: VideoCodecType,
    pub width: nat,
    pub height: nat,
    pub max_dpb_slots: nat,
    pub max_active_reference_pictures: nat,
}

/// Ghost state for a video decode session.
pub struct VideoSessionState {
    pub id: nat,
    pub profile: VideoProfileState,
    pub alive: bool,
}

/// State of a single DPB (decoded picture buffer) slot.
pub enum DpbSlotState {
    Empty,
    Active { image_view: nat, decode_order: nat },
}

/// Decoded picture buffer state.
pub struct DpbState {
    pub slots: Seq<DpbSlotState>,
    pub max_slots: nat,
}

/// A decode operation referencing a session and DPB.
pub struct DecodeOperation {
    pub session_id: nat,
    pub dst_image_view: nat,
    pub reference_slots: Set<nat>,
    pub output_slot: nat,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// A video profile is well-formed: positive dimensions, positive DPB slots.
pub open spec fn video_profile_well_formed(profile: VideoProfileState) -> bool {
    profile.width > 0
    && profile.height > 0
    && profile.max_dpb_slots > 0
    && profile.max_active_reference_pictures < profile.max_dpb_slots
}

/// A video session is well-formed: alive, profile well-formed.
pub open spec fn video_session_well_formed(state: VideoSessionState) -> bool {
    state.alive
    && video_profile_well_formed(state.profile)
}

/// DPB state is well-formed relative to a profile.
pub open spec fn dpb_state_well_formed(dpb: DpbState, profile: VideoProfileState) -> bool {
    dpb.slots.len() == dpb.max_slots
    && dpb.max_slots == profile.max_dpb_slots
}

/// Ghost: create a new video session.
pub open spec fn create_video_session_ghost(
    id: nat,
    profile: VideoProfileState,
) -> VideoSessionState {
    VideoSessionState { id, profile, alive: true }
}

/// Ghost: destroy a video session.
pub open spec fn destroy_video_session_ghost(
    state: VideoSessionState,
) -> VideoSessionState {
    VideoSessionState { alive: false, ..state }
}

/// Create an initial DPB with all Empty slots.
pub open spec fn dpb_initial(profile: VideoProfileState) -> DpbState {
    DpbState {
        slots: Seq::new(profile.max_dpb_slots, |_i: int| DpbSlotState::Empty),
        max_slots: profile.max_dpb_slots,
    }
}

/// Whether a DPB slot is active.
pub open spec fn dpb_slot_active(dpb: DpbState, idx: nat) -> bool {
    (idx as int) < dpb.slots.len()
    && match dpb.slots[idx as int] {
        DpbSlotState::Active { .. } => true,
        _ => false,
    }
}

/// All reference slots in a set are Active.
pub open spec fn dpb_reference_slots_valid(dpb: DpbState, refs: Set<nat>) -> bool {
    forall|idx: nat| refs.contains(idx) ==> dpb_slot_active(dpb, idx)
}

/// A decode operation is valid.
pub open spec fn decode_operation_valid(
    op: DecodeOperation,
    session: VideoSessionState,
    dpb: DpbState,
) -> bool {
    session.alive
    && session.id == op.session_id
    && (op.output_slot as int) < dpb.slots.len()
    && dpb_reference_slots_valid(dpb, op.reference_slots)
    && !op.reference_slots.contains(op.output_slot)
    && op.reference_slots.len() <= session.profile.max_active_reference_pictures
}

/// Ghost: perform a decode, activating the output slot.
pub open spec fn decode_ghost(op: DecodeOperation, dpb: DpbState) -> DpbState {
    DpbState {
        slots: dpb.slots.update(
            op.output_slot as int,
            DpbSlotState::Active {
                image_view: op.dst_image_view,
                decode_order: 0,
            },
        ),
        ..dpb
    }
}

/// Whether a DpbSlotState is Active.
pub open spec fn is_active_slot(slot: DpbSlotState) -> bool {
    match slot {
        DpbSlotState::Active { .. } => true,
        DpbSlotState::Empty => false,
    }
}

/// Count the number of Active slots in the DPB.
pub open spec fn dpb_active_count(dpb: DpbState) -> nat
    decreases dpb.slots.len(),
{
    if dpb.slots.len() == 0 {
        0
    } else {
        let last = dpb.slots.last();
        let rest = DpbState { slots: dpb.slots.drop_last(), ..dpb };
        dpb_active_count(rest) + if is_active_slot(last) { 1nat } else { 0nat }
    }
}

/// Ghost: reset a DPB slot to Empty.
pub open spec fn reset_dpb_slot_ghost(dpb: DpbState, idx: nat) -> DpbState {
    DpbState {
        slots: dpb.slots.update(idx as int, DpbSlotState::Empty),
        ..dpb
    }
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// Initial DPB has all Empty slots.
pub proof fn lemma_initial_dpb_all_empty(profile: VideoProfileState)
    requires profile.max_dpb_slots > 0,
    ensures
        forall|i: int| 0 <= i < dpb_initial(profile).slots.len()
            ==> dpb_initial(profile).slots[i] == DpbSlotState::Empty,
{
    let dpb = dpb_initial(profile);
    assert forall|i: int| 0 <= i < dpb.slots.len()
        implies dpb.slots[i] == DpbSlotState::Empty
    by {
        assert(dpb.slots[i] == DpbSlotState::Empty);
    }
}

/// Initial DPB is well-formed.
pub proof fn lemma_initial_dpb_well_formed(profile: VideoProfileState)
    requires video_profile_well_formed(profile),
    ensures dpb_state_well_formed(dpb_initial(profile), profile),
{
}

/// Created session is alive.
pub proof fn lemma_create_session_alive(id: nat, profile: VideoProfileState)
    ensures create_video_session_ghost(id, profile).alive,
{
}

/// Destroyed session is not alive.
pub proof fn lemma_destroy_session_not_alive(state: VideoSessionState)
    ensures !destroy_video_session_ghost(state).alive,
{
}

/// After decode, the output slot is Active.
pub proof fn lemma_decode_activates_slot(op: DecodeOperation, dpb: DpbState)
    requires (op.output_slot as int) < dpb.slots.len(),
    ensures dpb_slot_active(decode_ghost(op, dpb), op.output_slot),
{
}

/// Decode preserves reference slots (slots not equal to output_slot).
pub proof fn lemma_decode_preserves_references(
    op: DecodeOperation,
    dpb: DpbState,
    idx: nat,
)
    requires
        (op.output_slot as int) < dpb.slots.len(),
        idx != op.output_slot,
        (idx as int) < dpb.slots.len(),
    ensures decode_ghost(op, dpb).slots[idx as int] == dpb.slots[idx as int],
{
}

/// Active count is bounded by max_slots.
pub proof fn lemma_active_count_bounded(dpb: DpbState)
    ensures dpb_active_count(dpb) <= dpb.slots.len(),
    decreases dpb.slots.len(),
{
    if dpb.slots.len() > 0 {
        let rest = DpbState { slots: dpb.slots.drop_last(), ..dpb };
        lemma_active_count_bounded(rest);
    }
}

/// Valid decode implies output_slot is in range.
pub proof fn lemma_valid_decode_output_in_range(
    op: DecodeOperation,
    session: VideoSessionState,
    dpb: DpbState,
)
    requires decode_operation_valid(op, session, dpb),
    ensures (op.output_slot as int) < dpb.slots.len(),
{
}

/// Resetting an Active slot makes it Empty.
pub proof fn lemma_reset_makes_empty(dpb: DpbState, idx: nat)
    requires (idx as int) < dpb.slots.len(),
    ensures !dpb_slot_active(reset_dpb_slot_ghost(dpb, idx), idx),
{
}

/// Destroy preserves session id.
pub proof fn lemma_destroy_preserves_id(state: VideoSessionState)
    ensures destroy_video_session_ghost(state).id == state.id,
{
}

} // verus!
