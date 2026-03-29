use vstd::prelude::*;
use crate::resource::*;
use crate::flags::*;
use crate::sync::*;

verus! {

//  ── VK_KHR_synchronization2 ────────────────────────────────────────────
//
//  Models the Vulkan synchronization2 extension which provides:
//  - Per-barrier stage+access pairs (instead of per-command)
//  - VK_PIPELINE_STAGE_NONE / VK_ACCESS_NONE
//  - 64-bit stage and access flags
//  - Simplified barrier API

///  A single stage+access scope in sync2 style.
///  In sync1, stages and accesses are specified per-command.
///  In sync2, each barrier carries its own stage+access pair.
pub struct SyncScope2 {
    ///  Pipeline stages in this scope.
    pub stages: PipelineStageFlags,
    ///  Access types in this scope.
    pub accesses: AccessFlags,
}

///  A memory barrier in sync2 format.
///  Unlike sync1's VkMemoryBarrier which applies to all resources,
///  sync2 barriers carry their own stage+access scopes.
pub struct MemoryBarrier2 {
    ///  Source synchronization scope.
    pub src: SyncScope2,
    ///  Destination synchronization scope.
    pub dst: SyncScope2,
}

///  An image memory barrier in sync2 format.
pub struct ImageMemoryBarrier2 {
    ///  Source synchronization scope.
    pub src: SyncScope2,
    ///  Destination synchronization scope.
    pub dst: SyncScope2,
    ///  The image resource.
    pub resource: ResourceId,
    ///  Old image layout.
    pub old_layout: nat,
    ///  New image layout.
    pub new_layout: nat,
    ///  Source queue family index (for ownership transfer).
    pub src_queue_family: Option<nat>,
    ///  Destination queue family index (for ownership transfer).
    pub dst_queue_family: Option<nat>,
}

///  A buffer memory barrier in sync2 format.
pub struct BufferMemoryBarrier2 {
    ///  Source synchronization scope.
    pub src: SyncScope2,
    ///  Destination synchronization scope.
    pub dst: SyncScope2,
    ///  The buffer resource.
    pub resource: ResourceId,
    ///  Byte offset into the buffer.
    pub offset: nat,
    ///  Size of the region in bytes.
    pub size: nat,
    ///  Source queue family index (for ownership transfer).
    pub src_queue_family: Option<nat>,
    ///  Destination queue family index (for ownership transfer).
    pub dst_queue_family: Option<nat>,
}

///  A dependency info structure (sync2 replacement for vkCmdPipelineBarrier).
pub struct DependencyInfo {
    ///  Global memory barriers.
    pub memory_barriers: Seq<MemoryBarrier2>,
    ///  Buffer memory barriers.
    pub buffer_barriers: Seq<BufferMemoryBarrier2>,
    ///  Image memory barriers.
    pub image_barriers: Seq<ImageMemoryBarrier2>,
}

///  STAGE_NONE: no pipeline stage (sync2 concept).
///  Used to indicate no stage dependency.
pub open spec fn STAGE_NONE() -> nat { 100 }

///  ACCESS_NONE: no access type (sync2 concept).
///  Used for execution-only dependencies.
pub open spec fn ACCESS_NONE() -> nat { 100 }

//  ── Spec Functions ──────────────────────────────────────────────────────

///  A sync scope is empty (STAGE_NONE with ACCESS_NONE).
pub open spec fn scope_is_none(scope: SyncScope2) -> bool {
    scope.stages.stages.is_empty()
    && scope.accesses.accesses.is_empty()
}

///  A sync scope is execution-only (stages but no accesses).
pub open spec fn scope_is_execution_only(scope: SyncScope2) -> bool {
    !scope.stages.stages.is_empty()
    && scope.accesses.accesses.is_empty()
}

///  Convert a sync2 image barrier to a sync1-style BarrierEntry.
pub open spec fn image_barrier2_to_entry(ib: ImageMemoryBarrier2) -> BarrierEntry {
    BarrierEntry {
        resource: ib.resource,
        src_stages: ib.src.stages,
        src_accesses: ib.src.accesses,
        dst_stages: ib.dst.stages,
        dst_accesses: ib.dst.accesses,
    }
}

///  Convert a sync2 buffer barrier to a sync1-style BarrierEntry.
pub open spec fn buffer_barrier2_to_entry(bb: BufferMemoryBarrier2) -> BarrierEntry {
    BarrierEntry {
        resource: bb.resource,
        src_stages: bb.src.stages,
        src_accesses: bb.src.accesses,
        dst_stages: bb.dst.stages,
        dst_accesses: bb.dst.accesses,
    }
}

///  A dependency info is well-formed: all barriers have non-empty stages.
pub open spec fn dependency_info_well_formed(info: DependencyInfo) -> bool {
    (forall|i: nat|
        #![trigger info.memory_barriers[i as int]]
        i < info.memory_barriers.len()
        ==> !info.memory_barriers[i as int].src.stages.stages.is_empty()
            && !info.memory_barriers[i as int].dst.stages.stages.is_empty())
    && (forall|i: nat|
        #![trigger info.buffer_barriers[i as int]]
        i < info.buffer_barriers.len()
        ==> !info.buffer_barriers[i as int].src.stages.stages.is_empty()
            && !info.buffer_barriers[i as int].dst.stages.stages.is_empty())
    && (forall|i: nat|
        #![trigger info.image_barriers[i as int]]
        i < info.image_barriers.len()
        ==> !info.image_barriers[i as int].src.stages.stages.is_empty()
            && !info.image_barriers[i as int].dst.stages.stages.is_empty())
}

///  Whether an image barrier is a queue family ownership transfer.
pub open spec fn is_ownership_transfer(ib: ImageMemoryBarrier2) -> bool {
    ib.src_queue_family.is_some()
    && ib.dst_queue_family.is_some()
    && ib.src_queue_family != ib.dst_queue_family
}

///  Collect all barrier entries from a DependencyInfo into a flat log.
pub open spec fn dependency_info_to_log(info: DependencyInfo) -> BarrierLog {
    let buffer_entries = Seq::new(
        info.buffer_barriers.len(),
        |i: int| buffer_barrier2_to_entry(info.buffer_barriers[i]),
    );
    let image_entries = Seq::new(
        info.image_barriers.len(),
        |i: int| image_barrier2_to_entry(info.image_barriers[i]),
    );
    buffer_entries.add(image_entries)
}

//  ── Proofs ──────────────────────────────────────────────────────────────

///  Converting a sync2 barrier to sync1 preserves the resource.
pub proof fn lemma_image_barrier2_preserves_resource(ib: ImageMemoryBarrier2)
    ensures image_barrier2_to_entry(ib).resource == ib.resource,
{
}

///  An empty DependencyInfo is well-formed.
pub proof fn lemma_empty_dep_info_well_formed()
    ensures dependency_info_well_formed(DependencyInfo {
        memory_barriers: Seq::empty(),
        buffer_barriers: Seq::empty(),
        image_barriers: Seq::empty(),
    }),
{
}

///  An empty DependencyInfo produces an empty log.
pub proof fn lemma_empty_dep_info_empty_log()
    ensures dependency_info_to_log(DependencyInfo {
        memory_barriers: Seq::empty(),
        buffer_barriers: Seq::empty(),
        image_barriers: Seq::empty(),
    }).len() == 0,
{
}

///  A sync2 image barrier with matching stages/accesses creates a valid
///  sync1 barrier entry for read synchronization.
pub proof fn lemma_sync2_barrier_covers_sync1_read(
    ib: ImageMemoryBarrier2,
    state: SyncState,
    dst_stage: nat,
    dst_access: nat,
)
    requires
        resource_overlap(ib.resource, state.resource),
        stages_subset(state.write_stages, ib.src.stages),
        access_subset(state.write_accesses, ib.src.accesses),
        ib.dst.stages.stages.contains(dst_stage),
        ib.dst.accesses.accesses.contains(dst_access),
    ensures ({
        let entry = image_barrier2_to_entry(ib);
        resource_overlap(entry.resource, state.resource)
        && stages_subset(state.write_stages, entry.src_stages)
        && access_subset(state.write_accesses, entry.src_accesses)
        && entry.dst_stages.stages.contains(dst_stage)
        && entry.dst_accesses.accesses.contains(dst_access)
    }),
{
}

} //  verus!
