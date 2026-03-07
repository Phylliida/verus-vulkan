use vstd::prelude::*;
use crate::resource::*;
use crate::flags::*;
use crate::sync::*;

verus! {

// ── Constants ──────────────────────────────────────────────────────────

// Pipeline stage constants (matching Vulkan spec).
pub open spec fn STAGE_TOP_OF_PIPE() -> nat { 0 }
pub open spec fn STAGE_DRAW_INDIRECT() -> nat { 1 }
pub open spec fn STAGE_VERTEX_INPUT() -> nat { 2 }
pub open spec fn STAGE_VERTEX_SHADER() -> nat { 3 }
pub open spec fn STAGE_FRAGMENT_SHADER() -> nat { 4 }
pub open spec fn STAGE_EARLY_FRAGMENT_TESTS() -> nat { 5 }
pub open spec fn STAGE_LATE_FRAGMENT_TESTS() -> nat { 6 }
pub open spec fn STAGE_COLOR_ATTACHMENT_OUTPUT() -> nat { 7 }
pub open spec fn STAGE_COMPUTE_SHADER() -> nat { 8 }
pub open spec fn STAGE_TRANSFER() -> nat { 9 }
pub open spec fn STAGE_BOTTOM_OF_PIPE() -> nat { 10 }
pub open spec fn STAGE_HOST() -> nat { 11 }

// Access type constants (matching Vulkan spec).
pub open spec fn ACCESS_INDIRECT_COMMAND_READ() -> nat { 0 }
pub open spec fn ACCESS_INDEX_READ() -> nat { 1 }
pub open spec fn ACCESS_VERTEX_ATTRIBUTE_READ() -> nat { 2 }
pub open spec fn ACCESS_UNIFORM_READ() -> nat { 3 }
pub open spec fn ACCESS_INPUT_ATTACHMENT_READ() -> nat { 4 }
pub open spec fn ACCESS_SHADER_READ() -> nat { 5 }
pub open spec fn ACCESS_SHADER_WRITE() -> nat { 6 }
pub open spec fn ACCESS_COLOR_ATTACHMENT_READ() -> nat { 7 }
pub open spec fn ACCESS_COLOR_ATTACHMENT_WRITE() -> nat { 8 }
pub open spec fn ACCESS_DEPTH_STENCIL_ATTACHMENT_READ() -> nat { 9 }
pub open spec fn ACCESS_DEPTH_STENCIL_ATTACHMENT_WRITE() -> nat { 10 }
pub open spec fn ACCESS_TRANSFER_READ() -> nat { 11 }
pub open spec fn ACCESS_TRANSFER_WRITE() -> nat { 12 }
pub open spec fn ACCESS_HOST_READ() -> nat { 13 }
pub open spec fn ACCESS_HOST_WRITE() -> nat { 14 }
pub open spec fn ACCESS_MEMORY_READ() -> nat { 15 }
pub open spec fn ACCESS_MEMORY_WRITE() -> nat { 16 }

// ── Spec Functions ──────────────────────────────────────────────────────

/// Whether a (stage, access) pair is valid per the Vulkan spec.
/// Each access flag is only meaningful in specific pipeline stages.
pub open spec fn valid_stage_access(stage: nat, access: nat) -> bool {
    // MEMORY_READ and MEMORY_WRITE are valid in all stages
    access == ACCESS_MEMORY_READ() || access == ACCESS_MEMORY_WRITE()
    // TOP/BOTTOM of pipe: no specific accesses (only memory)
    || (stage == STAGE_DRAW_INDIRECT() && access == ACCESS_INDIRECT_COMMAND_READ())
    || (stage == STAGE_VERTEX_INPUT() && (
        access == ACCESS_INDEX_READ() || access == ACCESS_VERTEX_ATTRIBUTE_READ()))
    || (stage == STAGE_VERTEX_SHADER() && (
        access == ACCESS_UNIFORM_READ() || access == ACCESS_SHADER_READ() || access == ACCESS_SHADER_WRITE()))
    || (stage == STAGE_FRAGMENT_SHADER() && (
        access == ACCESS_UNIFORM_READ() || access == ACCESS_SHADER_READ()
        || access == ACCESS_SHADER_WRITE() || access == ACCESS_INPUT_ATTACHMENT_READ()))
    || (stage == STAGE_EARLY_FRAGMENT_TESTS() && (
        access == ACCESS_DEPTH_STENCIL_ATTACHMENT_READ() || access == ACCESS_DEPTH_STENCIL_ATTACHMENT_WRITE()))
    || (stage == STAGE_LATE_FRAGMENT_TESTS() && (
        access == ACCESS_DEPTH_STENCIL_ATTACHMENT_READ() || access == ACCESS_DEPTH_STENCIL_ATTACHMENT_WRITE()))
    || (stage == STAGE_COLOR_ATTACHMENT_OUTPUT() && (
        access == ACCESS_COLOR_ATTACHMENT_READ() || access == ACCESS_COLOR_ATTACHMENT_WRITE()))
    || (stage == STAGE_COMPUTE_SHADER() && (
        access == ACCESS_UNIFORM_READ() || access == ACCESS_SHADER_READ() || access == ACCESS_SHADER_WRITE()))
    || (stage == STAGE_TRANSFER() && (
        access == ACCESS_TRANSFER_READ() || access == ACCESS_TRANSFER_WRITE()))
    || (stage == STAGE_HOST() && (
        access == ACCESS_HOST_READ() || access == ACCESS_HOST_WRITE()))
}

/// All (stage, access) pairs in a barrier entry are valid.
pub open spec fn barrier_stage_access_valid(entry: BarrierEntry) -> bool {
    // Every src access must be valid with some src stage
    (forall|a: nat| entry.src_accesses.accesses.contains(a) ==>
        exists|s: nat| #[trigger] entry.src_stages.stages.contains(s) && valid_stage_access(s, a))
    // Every dst access must be valid with some dst stage
    && (forall|a: nat| entry.dst_accesses.accesses.contains(a) ==>
        exists|s: nat| #[trigger] entry.dst_stages.stages.contains(s) && valid_stage_access(s, a))
}

/// All barriers in a log have valid stage/access combinations.
pub open spec fn all_barriers_valid(log: Seq<BarrierEntry>) -> bool {
    forall|i: int| 0 <= i < log.len() ==> barrier_stage_access_valid(#[trigger] log[i])
}

/// A barrier with empty accesses is trivially valid.
pub open spec fn barrier_has_empty_accesses(entry: BarrierEntry) -> bool {
    entry.src_accesses.accesses == Set::<nat>::empty()
    && entry.dst_accesses.accesses == Set::<nat>::empty()
}

/// Execution-only barrier: stages but no accesses (pure execution dependency).
pub open spec fn execution_only_barrier(
    resource: ResourceId,
    src_stages: PipelineStageFlags,
    dst_stages: PipelineStageFlags,
) -> BarrierEntry {
    BarrierEntry {
        resource,
        src_stages,
        dst_stages,
        src_accesses: AccessFlags { accesses: Set::empty() },
        dst_accesses: AccessFlags { accesses: Set::empty() },
    }
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// An execution-only barrier is always valid (no accesses to check).
pub proof fn lemma_execution_only_barrier_valid(
    resource: ResourceId,
    src_stages: PipelineStageFlags,
    dst_stages: PipelineStageFlags,
)
    ensures
        barrier_stage_access_valid(execution_only_barrier(resource, src_stages, dst_stages)),
{
    let entry = execution_only_barrier(resource, src_stages, dst_stages);
    assert(entry.src_accesses.accesses == Set::<nat>::empty());
    assert(entry.dst_accesses.accesses == Set::<nat>::empty());
}

/// Memory read/write accesses are valid with any stage.
pub proof fn lemma_memory_access_any_stage(stage: nat, is_write: bool)
    ensures
        valid_stage_access(stage, ACCESS_MEMORY_READ()),
        valid_stage_access(stage, ACCESS_MEMORY_WRITE()),
{
}

/// A barrier with empty accesses is valid.
pub proof fn lemma_empty_accesses_valid(entry: BarrierEntry)
    requires barrier_has_empty_accesses(entry),
    ensures barrier_stage_access_valid(entry),
{
}

/// An empty barrier log is valid.
pub proof fn lemma_empty_log_valid()
    ensures all_barriers_valid(Seq::<BarrierEntry>::empty()),
{
}

/// Appending a valid barrier to a valid log preserves validity.
pub proof fn lemma_append_valid_barrier(
    log: Seq<BarrierEntry>,
    entry: BarrierEntry,
)
    requires
        all_barriers_valid(log),
        barrier_stage_access_valid(entry),
    ensures
        all_barriers_valid(log.push(entry)),
{
    assert forall|i: int| 0 <= i < log.push(entry).len()
    implies barrier_stage_access_valid(log.push(entry)[i]) by {
        if i < log.len() as int {
            assert(log.push(entry)[i] == log[i]);
        } else {
            assert(log.push(entry)[i] == entry);
        }
    }
}

/// A transfer barrier with transfer read/write is valid.
pub proof fn lemma_transfer_barrier_valid(resource: ResourceId)
    ensures barrier_stage_access_valid(BarrierEntry {
        resource,
        src_stages: PipelineStageFlags { stages: Set::empty().insert(STAGE_TRANSFER()) },
        src_accesses: AccessFlags { accesses: Set::empty().insert(ACCESS_TRANSFER_WRITE()) },
        dst_stages: PipelineStageFlags { stages: Set::empty().insert(STAGE_TRANSFER()) },
        dst_accesses: AccessFlags { accesses: Set::empty().insert(ACCESS_TRANSFER_READ()) },
    }),
{
    let entry = BarrierEntry {
        resource,
        src_stages: PipelineStageFlags { stages: Set::empty().insert(STAGE_TRANSFER()) },
        src_accesses: AccessFlags { accesses: Set::empty().insert(ACCESS_TRANSFER_WRITE()) },
        dst_stages: PipelineStageFlags { stages: Set::empty().insert(STAGE_TRANSFER()) },
        dst_accesses: AccessFlags { accesses: Set::empty().insert(ACCESS_TRANSFER_READ()) },
    };
    // Help Z3 with the existential: for each access, show the stage that makes it valid
    assert forall|a: nat| entry.src_accesses.accesses.contains(a)
    implies exists|s: nat| #[trigger] entry.src_stages.stages.contains(s) && valid_stage_access(s, a) by {
        assert(entry.src_stages.stages.contains(STAGE_TRANSFER()));
        assert(valid_stage_access(STAGE_TRANSFER(), ACCESS_TRANSFER_WRITE()));
    }
    assert forall|a: nat| entry.dst_accesses.accesses.contains(a)
    implies exists|s: nat| #[trigger] entry.dst_stages.stages.contains(s) && valid_stage_access(s, a) by {
        assert(entry.dst_stages.stages.contains(STAGE_TRANSFER()));
        assert(valid_stage_access(STAGE_TRANSFER(), ACCESS_TRANSFER_READ()));
    }
}

/// A color attachment write → shader read barrier is valid.
pub proof fn lemma_color_to_shader_read_valid(resource: ResourceId)
    ensures barrier_stage_access_valid(BarrierEntry {
        resource,
        src_stages: PipelineStageFlags { stages: Set::empty().insert(STAGE_COLOR_ATTACHMENT_OUTPUT()) },
        src_accesses: AccessFlags { accesses: Set::empty().insert(ACCESS_COLOR_ATTACHMENT_WRITE()) },
        dst_stages: PipelineStageFlags { stages: Set::empty().insert(STAGE_FRAGMENT_SHADER()) },
        dst_accesses: AccessFlags { accesses: Set::empty().insert(ACCESS_SHADER_READ()) },
    }),
{
    let entry = BarrierEntry {
        resource,
        src_stages: PipelineStageFlags { stages: Set::empty().insert(STAGE_COLOR_ATTACHMENT_OUTPUT()) },
        src_accesses: AccessFlags { accesses: Set::empty().insert(ACCESS_COLOR_ATTACHMENT_WRITE()) },
        dst_stages: PipelineStageFlags { stages: Set::empty().insert(STAGE_FRAGMENT_SHADER()) },
        dst_accesses: AccessFlags { accesses: Set::empty().insert(ACCESS_SHADER_READ()) },
    };
    assert(entry.src_stages.stages.contains(STAGE_COLOR_ATTACHMENT_OUTPUT()));
    assert(entry.dst_stages.stages.contains(STAGE_FRAGMENT_SHADER()));
}

} // verus!
