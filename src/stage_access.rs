use vstd::prelude::*;
use crate::resource::*;
use crate::flags::*;
use crate::sync::*;

verus! {

// Stage and access constants are now defined in flags.rs (single source of truth).
// They are imported via `use crate::flags::*` above.

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

/// Shader write access at vertex shader stage is valid.
pub proof fn lemma_vertex_shader_write_valid()
    ensures valid_stage_access(STAGE_VERTEX_SHADER(), ACCESS_SHADER_WRITE()),
{
}

/// Shader write access at compute shader stage is valid.
pub proof fn lemma_compute_shader_write_valid()
    ensures valid_stage_access(STAGE_COMPUTE_SHADER(), ACCESS_SHADER_WRITE()),
{
}

/// Depth/stencil attachment access at early fragment tests is valid.
pub proof fn lemma_early_depth_access_valid()
    ensures
        valid_stage_access(STAGE_EARLY_FRAGMENT_TESTS(), ACCESS_DEPTH_STENCIL_ATTACHMENT_READ()),
        valid_stage_access(STAGE_EARLY_FRAGMENT_TESTS(), ACCESS_DEPTH_STENCIL_ATTACHMENT_WRITE()),
{
}

/// Color attachment access at color output stage is valid.
pub proof fn lemma_color_output_access_valid()
    ensures
        valid_stage_access(STAGE_COLOR_ATTACHMENT_OUTPUT(), ACCESS_COLOR_ATTACHMENT_READ()),
        valid_stage_access(STAGE_COLOR_ATTACHMENT_OUTPUT(), ACCESS_COLOR_ATTACHMENT_WRITE()),
{
}

/// Host access at host stage is valid.
pub proof fn lemma_host_access_valid()
    ensures
        valid_stage_access(STAGE_HOST(), ACCESS_HOST_READ()),
        valid_stage_access(STAGE_HOST(), ACCESS_HOST_WRITE()),
{
}

/// A sub-log (prefix) of a valid log is valid.
pub proof fn lemma_prefix_valid(log: Seq<BarrierEntry>, n: nat)
    requires
        all_barriers_valid(log),
        n <= log.len(),
    ensures
        all_barriers_valid(log.subrange(0, n as int)),
{
    let prefix = log.subrange(0, n as int);
    assert forall|i: int| 0 <= i < prefix.len()
    implies barrier_stage_access_valid(prefix[i]) by {
        assert(prefix[i] == log[i]);
    }
}

/// Concatenating two valid barrier logs produces a valid log.
pub proof fn lemma_concat_valid_logs(
    log1: Seq<BarrierEntry>,
    log2: Seq<BarrierEntry>,
)
    requires
        all_barriers_valid(log1),
        all_barriers_valid(log2),
    ensures
        all_barriers_valid(log1.add(log2)),
{
    let combined = log1.add(log2);
    assert forall|i: int| 0 <= i < combined.len()
    implies barrier_stage_access_valid(combined[i]) by {
        if i < log1.len() as int {
            assert(combined[i] == log1[i]);
        } else {
            assert(combined[i] == log2[i - log1.len() as int]);
        }
    }
}

// ── Queue Capability Validation ─────────────────────────────────────────

/// Capabilities of a queue family.
pub struct QueueCapabilities {
    pub graphics: bool,
    pub compute: bool,
    pub transfer: bool,
}

/// Whether a pipeline stage is supported by a queue with the given capabilities.
/// TOP_OF_PIPE, BOTTOM_OF_PIPE, TRANSFER, and HOST are always supported.
/// Graphics stages require graphics capability; compute requires compute capability.
pub open spec fn stage_supported_by_queue(stage: nat, caps: QueueCapabilities) -> bool {
    stage == STAGE_TOP_OF_PIPE() || stage == STAGE_BOTTOM_OF_PIPE()
    || stage == STAGE_TRANSFER() || stage == STAGE_HOST()
    || (caps.graphics && (
        stage == STAGE_DRAW_INDIRECT() || stage == STAGE_VERTEX_INPUT()
        || stage == STAGE_VERTEX_SHADER() || stage == STAGE_FRAGMENT_SHADER()
        || stage == STAGE_EARLY_FRAGMENT_TESTS() || stage == STAGE_LATE_FRAGMENT_TESTS()
        || stage == STAGE_COLOR_ATTACHMENT_OUTPUT()
    ))
    || (caps.compute && stage == STAGE_COMPUTE_SHADER())
}

/// All stages in a barrier entry are supported by the queue.
pub open spec fn barrier_stages_supported(entry: BarrierEntry, caps: QueueCapabilities) -> bool {
    (forall|s: nat| entry.src_stages.stages.contains(s) ==> stage_supported_by_queue(s, caps))
    && (forall|s: nat| entry.dst_stages.stages.contains(s) ==> stage_supported_by_queue(s, caps))
}

/// A transfer-only queue supports only TOP_OF_PIPE, BOTTOM_OF_PIPE, TRANSFER, and HOST.
pub proof fn lemma_transfer_queue_stages(stage: nat)
    requires
        stage_supported_by_queue(stage, QueueCapabilities { graphics: false, compute: false, transfer: true }),
    ensures
        stage == STAGE_TOP_OF_PIPE() || stage == STAGE_BOTTOM_OF_PIPE()
        || stage == STAGE_TRANSFER() || stage == STAGE_HOST(),
{
}

/// A graphics+compute+transfer queue supports all defined stages.
pub proof fn lemma_graphics_queue_all_stages(stage: nat)
    requires
        stage == STAGE_TOP_OF_PIPE() || stage == STAGE_BOTTOM_OF_PIPE()
        || stage == STAGE_TRANSFER() || stage == STAGE_HOST()
        || stage == STAGE_DRAW_INDIRECT() || stage == STAGE_VERTEX_INPUT()
        || stage == STAGE_VERTEX_SHADER() || stage == STAGE_FRAGMENT_SHADER()
        || stage == STAGE_EARLY_FRAGMENT_TESTS() || stage == STAGE_LATE_FRAGMENT_TESTS()
        || stage == STAGE_COLOR_ATTACHMENT_OUTPUT()
        || stage == STAGE_COMPUTE_SHADER(),
    ensures
        stage_supported_by_queue(stage, QueueCapabilities { graphics: true, compute: true, transfer: true }),
{
}

/// Indirect command read at draw indirect stage is valid.
pub proof fn lemma_indirect_command_read_valid()
    ensures valid_stage_access(STAGE_DRAW_INDIRECT(), ACCESS_INDIRECT_COMMAND_READ()),
{
}

/// Index and vertex attribute reads at vertex input stage are valid.
pub proof fn lemma_vertex_input_reads_valid()
    ensures
        valid_stage_access(STAGE_VERTEX_INPUT(), ACCESS_INDEX_READ()),
        valid_stage_access(STAGE_VERTEX_INPUT(), ACCESS_VERTEX_ATTRIBUTE_READ()),
{
}

} // verus!
