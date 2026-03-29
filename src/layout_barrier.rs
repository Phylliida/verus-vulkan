use vstd::prelude::*;
use crate::sync::*;
use crate::sync_proofs::*;
use crate::flags::*;
use crate::resource::*;
use crate::image_layout::*;
use crate::image_layout_fsm::*;
use crate::recording_commands::*;

verus! {

//  ── Types ───────────────────────────────────────────────────────────────

///  Combined image memory barrier: sync + layout transition in one call.
///
///  In Vulkan, VkImageMemoryBarrier performs both synchronization (execution +
///  memory dependency) and an image layout transition atomically. This struct
///  unifies the currently-separate BarrierEntry (sync.rs) and ImageLayoutMap
///  (image_layout_fsm.rs) models.
pub struct ImageBarrierEntry {
    ///  The synchronization half (stages + accesses + resource).
    pub sync: BarrierEntry,
    ///  Image layout before the barrier.
    pub old_layout: ImageLayout,
    ///  Image layout after the barrier.
    pub new_layout: ImageLayout,
}

//  ── Spec Functions ──────────────────────────────────────────────────────

///  Extract the sync half of an image barrier.
pub open spec fn image_barrier_to_entry(ibe: ImageBarrierEntry) -> BarrierEntry {
    ibe.sync
}

///  Apply the layout transition half of an image barrier to a layout map.
pub open spec fn image_barrier_apply_layout(
    ibe: ImageBarrierEntry,
    layout_map: ImageLayoutMap,
) -> ImageLayoutMap {
    apply_layout_transition(layout_map, ibe.sync.resource, ibe.new_layout)
}

///  An image barrier is well-formed: the layout transition is valid
///  (new_layout is a usable layout).
pub open spec fn image_barrier_well_formed(ibe: ImageBarrierEntry) -> bool {
    layout_transition_valid(ibe.old_layout, ibe.new_layout)
}

//  ── Proofs ──────────────────────────────────────────────────────────────

///  A well-formed image barrier that covers a last write establishes both
///  readability (via sync) AND the new layout (via transition).
pub proof fn lemma_image_barrier_establishes_readable_and_layout(
    ctx: RecordingContext,
    ibe: ImageBarrierEntry,
    state: SyncState,
    dst_stage: nat,
    dst_access: nat,
    layout_map: ImageLayoutMap,
)
    requires
        image_barrier_well_formed(ibe),
        state.last_write.is_some(),
        resource_overlap(ibe.sync.resource, state.resource),
        stages_subset(state.write_stages, ibe.sync.src_stages),
        access_subset(state.write_accesses, ibe.sync.src_accesses),
        ibe.sync.dst_stages.stages.contains(dst_stage),
        ibe.sync.dst_accesses.accesses.contains(dst_access),
    ensures
        readable(
            record_pipeline_barrier_single(ctx, ibe.sync).barrier_log,
            state,
            dst_stage,
            dst_access,
        ),
        has_layout(
            image_barrier_apply_layout(ibe, layout_map),
            ibe.sync.resource,
            ibe.new_layout,
        ),
{
    lemma_barrier_establishes_readable(ctx, ibe.sync, state, dst_stage, dst_access);
    lemma_transition_updates_target(layout_map, ibe.sync.resource, ibe.new_layout);
}

///  A well-formed image barrier that covers both last write and readers
///  establishes both writability (via sync) AND the new layout (via transition).
pub proof fn lemma_image_barrier_establishes_writable_and_layout(
    ctx: RecordingContext,
    ibe: ImageBarrierEntry,
    state: SyncState,
    dst_stage: nat,
    dst_access: nat,
    layout_map: ImageLayoutMap,
)
    requires
        image_barrier_well_formed(ibe),
        state.last_write.is_some() || state.last_reads.len() > 0,
        resource_overlap(ibe.sync.resource, state.resource),
        stages_subset(state.write_stages, ibe.sync.src_stages),
        access_subset(state.write_accesses, ibe.sync.src_accesses),
        stages_subset(state.read_stages, ibe.sync.src_stages),
        access_subset(state.read_accesses, ibe.sync.src_accesses),
        ibe.sync.dst_stages.stages.contains(dst_stage),
        ibe.sync.dst_accesses.accesses.contains(dst_access),
    ensures
        writable(
            record_pipeline_barrier_single(ctx, ibe.sync).barrier_log,
            state,
            dst_stage,
            dst_access,
        ),
        has_layout(
            image_barrier_apply_layout(ibe, layout_map),
            ibe.sync.resource,
            ibe.new_layout,
        ),
{
    lemma_barrier_establishes_writable(ctx, ibe.sync, state, dst_stage, dst_access);
    lemma_transition_updates_target(layout_map, ibe.sync.resource, ibe.new_layout);
}

///  An image barrier's layout transition does not affect other resources.
pub proof fn lemma_image_barrier_preserves_other_layouts(
    ibe: ImageBarrierEntry,
    layout_map: ImageLayoutMap,
    other: ResourceId,
)
    requires
        other != ibe.sync.resource,
        layout_map.contains_key(other),
    ensures
        image_barrier_apply_layout(ibe, layout_map).contains_key(other),
        image_barrier_apply_layout(ibe, layout_map)[other] == layout_map[other],
{
    lemma_transition_preserves_others(layout_map, ibe.sync.resource, ibe.new_layout, other);
}

} //  verus!
