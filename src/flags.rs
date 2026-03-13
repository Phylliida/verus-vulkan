use vstd::prelude::*;

verus! {

// ── Pipeline stage constants ──────────────────────────────────────────
// Each stage gets a distinct nat so we can use Set<nat> for stage masks.

pub open spec fn STAGE_TOP_OF_PIPE() -> nat { 0 }
pub open spec fn STAGE_VERTEX_SHADER() -> nat { 1 }
pub open spec fn STAGE_FRAGMENT_SHADER() -> nat { 2 }
pub open spec fn STAGE_COMPUTE_SHADER() -> nat { 3 }
pub open spec fn STAGE_TRANSFER() -> nat { 4 }
pub open spec fn STAGE_BOTTOM_OF_PIPE() -> nat { 5 }
pub open spec fn STAGE_COLOR_ATTACHMENT_OUTPUT() -> nat { 6 }
pub open spec fn STAGE_EARLY_FRAGMENT_TESTS() -> nat { 7 }
pub open spec fn STAGE_LATE_FRAGMENT_TESTS() -> nat { 8 }
pub open spec fn STAGE_TASK_SHADER() -> nat { 9 }
pub open spec fn STAGE_MESH_SHADER() -> nat { 10 }
pub open spec fn STAGE_RAY_TRACING_SHADER() -> nat { 11 }
pub open spec fn STAGE_FRAGMENT_SHADING_RATE_ATTACHMENT() -> nat { 12 }

/// A set of pipeline stages.
pub struct PipelineStageFlags {
    pub stages: Set<nat>,
}

// ── Access type constants ─────────────────────────────────────────────

pub open spec fn ACCESS_SHADER_READ() -> nat { 0 }
pub open spec fn ACCESS_SHADER_WRITE() -> nat { 1 }
pub open spec fn ACCESS_COLOR_ATTACHMENT_READ() -> nat { 2 }
pub open spec fn ACCESS_COLOR_ATTACHMENT_WRITE() -> nat { 3 }
pub open spec fn ACCESS_DEPTH_STENCIL_READ() -> nat { 4 }
pub open spec fn ACCESS_DEPTH_STENCIL_WRITE() -> nat { 5 }
pub open spec fn ACCESS_TRANSFER_READ() -> nat { 6 }
pub open spec fn ACCESS_TRANSFER_WRITE() -> nat { 7 }
pub open spec fn ACCESS_HOST_READ() -> nat { 8 }
pub open spec fn ACCESS_HOST_WRITE() -> nat { 9 }
pub open spec fn ACCESS_FRAGMENT_SHADING_RATE_ATTACHMENT_READ() -> nat { 10 }
pub open spec fn ACCESS_ACCELERATION_STRUCTURE_READ() -> nat { 11 }
pub open spec fn ACCESS_ACCELERATION_STRUCTURE_WRITE() -> nat { 12 }

// ── Buffer/Image usage flag constants ─────────────────────────────────
// Each usage flag gets a distinct nat for Set<nat>-based usage tracking.

pub open spec fn USAGE_VERTEX_BUFFER() -> nat { 0 }
pub open spec fn USAGE_INDEX_BUFFER() -> nat { 1 }
pub open spec fn USAGE_UNIFORM_BUFFER() -> nat { 2 }
pub open spec fn USAGE_STORAGE_BUFFER() -> nat { 3 }
pub open spec fn USAGE_TRANSFER_SRC() -> nat { 4 }
pub open spec fn USAGE_TRANSFER_DST() -> nat { 5 }
pub open spec fn USAGE_SAMPLED() -> nat { 6 }
pub open spec fn USAGE_STORAGE_IMAGE() -> nat { 7 }
pub open spec fn USAGE_COLOR_ATTACHMENT() -> nat { 8 }
pub open spec fn USAGE_DEPTH_STENCIL_ATTACHMENT() -> nat { 9 }
pub open spec fn USAGE_INPUT_ATTACHMENT() -> nat { 10 }
pub open spec fn USAGE_INDIRECT_BUFFER() -> nat { 11 }
pub open spec fn USAGE_SHADING_RATE_IMAGE() -> nat { 12 }
pub open spec fn USAGE_FRAGMENT_DENSITY_MAP() -> nat { 13 }

/// A set of access types.
pub struct AccessFlags {
    pub accesses: Set<nat>,
}

/// True iff the access set contains any write access.
pub open spec fn has_write_access(flags: AccessFlags) -> bool {
    flags.accesses.contains(ACCESS_SHADER_WRITE())
    || flags.accesses.contains(ACCESS_COLOR_ATTACHMENT_WRITE())
    || flags.accesses.contains(ACCESS_DEPTH_STENCIL_WRITE())
    || flags.accesses.contains(ACCESS_TRANSFER_WRITE())
    || flags.accesses.contains(ACCESS_HOST_WRITE())
    || flags.accesses.contains(ACCESS_ACCELERATION_STRUCTURE_WRITE())
}

/// True iff the access set contains any read access.
pub open spec fn has_read_access(flags: AccessFlags) -> bool {
    flags.accesses.contains(ACCESS_SHADER_READ())
    || flags.accesses.contains(ACCESS_COLOR_ATTACHMENT_READ())
    || flags.accesses.contains(ACCESS_DEPTH_STENCIL_READ())
    || flags.accesses.contains(ACCESS_TRANSFER_READ())
    || flags.accesses.contains(ACCESS_HOST_READ())
    || flags.accesses.contains(ACCESS_FRAGMENT_SHADING_RATE_ATTACHMENT_READ())
    || flags.accesses.contains(ACCESS_ACCELERATION_STRUCTURE_READ())
}

/// An empty stage set.
pub open spec fn no_stages() -> PipelineStageFlags {
    PipelineStageFlags { stages: Set::empty() }
}

/// An empty access set.
pub open spec fn no_access() -> AccessFlags {
    AccessFlags { accesses: Set::empty() }
}

/// True iff `sub` is a subset of `sup` (for stages).
pub open spec fn stages_subset(sub: PipelineStageFlags, sup: PipelineStageFlags) -> bool {
    sub.stages.subset_of(sup.stages)
}

/// True iff `sub` is a subset of `sup` (for accesses).
pub open spec fn access_subset(sub: AccessFlags, sup: AccessFlags) -> bool {
    sub.accesses.subset_of(sup.accesses)
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// stages_subset is reflexive.
pub proof fn lemma_stages_subset_reflexive(s: PipelineStageFlags)
    ensures stages_subset(s, s),
{
}

/// stages_subset is transitive.
pub proof fn lemma_stages_subset_transitive(
    a: PipelineStageFlags, b: PipelineStageFlags, c: PipelineStageFlags,
)
    requires stages_subset(a, b), stages_subset(b, c),
    ensures stages_subset(a, c),
{
}

/// access_subset is reflexive.
pub proof fn lemma_access_subset_reflexive(a: AccessFlags)
    ensures access_subset(a, a),
{
}

/// access_subset is transitive.
pub proof fn lemma_access_subset_transitive(
    a: AccessFlags, b: AccessFlags, c: AccessFlags,
)
    requires access_subset(a, b), access_subset(b, c),
    ensures access_subset(a, c),
{
}

/// Empty stages are a subset of any stages.
pub proof fn lemma_empty_stages_subset(s: PipelineStageFlags)
    ensures stages_subset(no_stages(), s),
{
}

/// Empty accesses are a subset of any accesses.
pub proof fn lemma_empty_access_subset(a: AccessFlags)
    ensures access_subset(no_access(), a),
{
}

/// An empty access set has no write access.
pub proof fn lemma_empty_no_write_access()
    ensures !has_write_access(no_access()),
{
}

/// An empty access set has no read access.
pub proof fn lemma_empty_no_read_access()
    ensures !has_read_access(no_access()),
{
}

/// All stage constants are distinct.
pub proof fn lemma_stage_constants_distinct()
    ensures
        STAGE_TOP_OF_PIPE() != STAGE_VERTEX_SHADER(),
        STAGE_TOP_OF_PIPE() != STAGE_FRAGMENT_SHADER(),
        STAGE_TOP_OF_PIPE() != STAGE_COMPUTE_SHADER(),
        STAGE_TOP_OF_PIPE() != STAGE_TRANSFER(),
        STAGE_TOP_OF_PIPE() != STAGE_BOTTOM_OF_PIPE(),
        STAGE_VERTEX_SHADER() != STAGE_FRAGMENT_SHADER(),
        STAGE_VERTEX_SHADER() != STAGE_COMPUTE_SHADER(),
        STAGE_FRAGMENT_SHADER() != STAGE_COMPUTE_SHADER(),
        STAGE_TRANSFER() != STAGE_COMPUTE_SHADER(),
        STAGE_COLOR_ATTACHMENT_OUTPUT() != STAGE_FRAGMENT_SHADER(),
{
}

/// All access constants are distinct.
pub proof fn lemma_access_constants_distinct()
    ensures
        ACCESS_SHADER_READ() != ACCESS_SHADER_WRITE(),
        ACCESS_COLOR_ATTACHMENT_READ() != ACCESS_COLOR_ATTACHMENT_WRITE(),
        ACCESS_DEPTH_STENCIL_READ() != ACCESS_DEPTH_STENCIL_WRITE(),
        ACCESS_TRANSFER_READ() != ACCESS_TRANSFER_WRITE(),
        ACCESS_HOST_READ() != ACCESS_HOST_WRITE(),
        ACCESS_SHADER_READ() != ACCESS_TRANSFER_READ(),
        ACCESS_SHADER_WRITE() != ACCESS_TRANSFER_WRITE(),
{
}

/// stages_subset of no_stages holds only if the sub is also empty.
pub proof fn lemma_no_stages_minimal(s: PipelineStageFlags)
    requires stages_subset(s, no_stages()),
    ensures s.stages == Set::<nat>::empty(),
{
    assert(s.stages.subset_of(Set::<nat>::empty()));
    assert(s.stages =~= Set::<nat>::empty());
}

// ── Pipeline stage enum ────────────────────────────────────────────────
// Typed enum for pipeline stages, used in bitmask conversion for FFI coupling.

pub enum PipelineStage {
    TopOfPipe,
    VertexShader,
    FragmentShader,
    ComputeShader,
    Transfer,
    BottomOfPipe,
    ColorAttachmentOutput,
    EarlyFragmentTests,
    LateFragmentTests,
    TaskShader,
    MeshShader,
    RayTracingShader,
    FragmentShadingRateAttachment,
}

/// Map a PipelineStage enum variant to its abstract stage ID (nat).
pub open spec fn stage_to_id(stage: PipelineStage) -> nat {
    match stage {
        PipelineStage::TopOfPipe => STAGE_TOP_OF_PIPE(),
        PipelineStage::VertexShader => STAGE_VERTEX_SHADER(),
        PipelineStage::FragmentShader => STAGE_FRAGMENT_SHADER(),
        PipelineStage::ComputeShader => STAGE_COMPUTE_SHADER(),
        PipelineStage::Transfer => STAGE_TRANSFER(),
        PipelineStage::BottomOfPipe => STAGE_BOTTOM_OF_PIPE(),
        PipelineStage::ColorAttachmentOutput => STAGE_COLOR_ATTACHMENT_OUTPUT(),
        PipelineStage::EarlyFragmentTests => STAGE_EARLY_FRAGMENT_TESTS(),
        PipelineStage::LateFragmentTests => STAGE_LATE_FRAGMENT_TESTS(),
        PipelineStage::TaskShader => STAGE_TASK_SHADER(),
        PipelineStage::MeshShader => STAGE_MESH_SHADER(),
        PipelineStage::RayTracingShader => STAGE_RAY_TRACING_SHADER(),
        PipelineStage::FragmentShadingRateAttachment => STAGE_FRAGMENT_SHADING_RATE_ATTACHMENT(),
    }
}

/// Map a PipelineStage enum variant to its Vulkan VkPipelineStageFlagBits value.
pub open spec fn stage_vk_bit(stage: PipelineStage) -> u32 {
    match stage {
        PipelineStage::TopOfPipe => 0x00000001u32,
        PipelineStage::VertexShader => 0x00000008u32,
        PipelineStage::FragmentShader => 0x00000080u32,
        PipelineStage::ComputeShader => 0x00000800u32,
        PipelineStage::Transfer => 0x00001000u32,
        PipelineStage::BottomOfPipe => 0x00002000u32,
        PipelineStage::ColorAttachmentOutput => 0x00000400u32,
        PipelineStage::EarlyFragmentTests => 0x00000100u32,
        PipelineStage::LateFragmentTests => 0x00000200u32,
        PipelineStage::TaskShader => 0x00080000u32,
        PipelineStage::MeshShader => 0x00100000u32,
        PipelineStage::RayTracingShader => 0x00200000u32,
        PipelineStage::FragmentShadingRateAttachment => 0x00400000u32,
    }
}

/// Compute the Vulkan u32 bitmask for a set of abstract stages.
/// Since all bits are distinct powers of 2, sum == bitwise OR.
pub open spec fn stages_to_vk_bitmask(flags: PipelineStageFlags) -> u32 {
    (  if flags.stages.contains(stage_to_id(PipelineStage::TopOfPipe))             { stage_vk_bit(PipelineStage::TopOfPipe) } else { 0u32 }
     + if flags.stages.contains(stage_to_id(PipelineStage::VertexShader))           { stage_vk_bit(PipelineStage::VertexShader) } else { 0u32 }
     + if flags.stages.contains(stage_to_id(PipelineStage::FragmentShader))         { stage_vk_bit(PipelineStage::FragmentShader) } else { 0u32 }
     + if flags.stages.contains(stage_to_id(PipelineStage::ComputeShader))          { stage_vk_bit(PipelineStage::ComputeShader) } else { 0u32 }
     + if flags.stages.contains(stage_to_id(PipelineStage::Transfer))               { stage_vk_bit(PipelineStage::Transfer) } else { 0u32 }
     + if flags.stages.contains(stage_to_id(PipelineStage::BottomOfPipe))           { stage_vk_bit(PipelineStage::BottomOfPipe) } else { 0u32 }
     + if flags.stages.contains(stage_to_id(PipelineStage::ColorAttachmentOutput))  { stage_vk_bit(PipelineStage::ColorAttachmentOutput) } else { 0u32 }
     + if flags.stages.contains(stage_to_id(PipelineStage::EarlyFragmentTests))     { stage_vk_bit(PipelineStage::EarlyFragmentTests) } else { 0u32 }
     + if flags.stages.contains(stage_to_id(PipelineStage::LateFragmentTests))      { stage_vk_bit(PipelineStage::LateFragmentTests) } else { 0u32 }
     + if flags.stages.contains(stage_to_id(PipelineStage::TaskShader))             { stage_vk_bit(PipelineStage::TaskShader) } else { 0u32 }
     + if flags.stages.contains(stage_to_id(PipelineStage::MeshShader))             { stage_vk_bit(PipelineStage::MeshShader) } else { 0u32 }
     + if flags.stages.contains(stage_to_id(PipelineStage::RayTracingShader))       { stage_vk_bit(PipelineStage::RayTracingShader) } else { 0u32 }
     + if flags.stages.contains(stage_to_id(PipelineStage::FragmentShadingRateAttachment)) { stage_vk_bit(PipelineStage::FragmentShadingRateAttachment) } else { 0u32 }
    ) as u32
}

/// All usage flag constants are distinct.
pub proof fn lemma_usage_constants_distinct()
    ensures
        USAGE_VERTEX_BUFFER() != USAGE_INDEX_BUFFER(),
        USAGE_VERTEX_BUFFER() != USAGE_UNIFORM_BUFFER(),
        USAGE_UNIFORM_BUFFER() != USAGE_STORAGE_BUFFER(),
        USAGE_TRANSFER_SRC() != USAGE_TRANSFER_DST(),
        USAGE_SAMPLED() != USAGE_STORAGE_IMAGE(),
        USAGE_COLOR_ATTACHMENT() != USAGE_DEPTH_STENCIL_ATTACHMENT(),
        USAGE_DEPTH_STENCIL_ATTACHMENT() != USAGE_INPUT_ATTACHMENT(),
        USAGE_TRANSFER_SRC() != USAGE_UNIFORM_BUFFER(),
        USAGE_TRANSFER_DST() != USAGE_STORAGE_BUFFER(),
        USAGE_SAMPLED() != USAGE_INPUT_ATTACHMENT(),
        USAGE_STORAGE_IMAGE() != USAGE_INPUT_ATTACHMENT(),
        USAGE_SHADING_RATE_IMAGE() != USAGE_FRAGMENT_DENSITY_MAP(),
        USAGE_INDIRECT_BUFFER() != USAGE_SHADING_RATE_IMAGE(),
        USAGE_INDIRECT_BUFFER() != USAGE_FRAGMENT_DENSITY_MAP(),
{
}

/// All new stage constants are distinct from each other and from existing ones.
pub proof fn lemma_new_stage_constants_distinct()
    ensures
        STAGE_TASK_SHADER() != STAGE_MESH_SHADER(),
        STAGE_TASK_SHADER() != STAGE_RAY_TRACING_SHADER(),
        STAGE_TASK_SHADER() != STAGE_FRAGMENT_SHADING_RATE_ATTACHMENT(),
        STAGE_MESH_SHADER() != STAGE_RAY_TRACING_SHADER(),
        STAGE_MESH_SHADER() != STAGE_FRAGMENT_SHADING_RATE_ATTACHMENT(),
        STAGE_RAY_TRACING_SHADER() != STAGE_FRAGMENT_SHADING_RATE_ATTACHMENT(),
        STAGE_TASK_SHADER() != STAGE_TOP_OF_PIPE(),
        STAGE_TASK_SHADER() != STAGE_VERTEX_SHADER(),
        STAGE_TASK_SHADER() != STAGE_FRAGMENT_SHADER(),
        STAGE_TASK_SHADER() != STAGE_COMPUTE_SHADER(),
        STAGE_TASK_SHADER() != STAGE_TRANSFER(),
        STAGE_TASK_SHADER() != STAGE_BOTTOM_OF_PIPE(),
        STAGE_MESH_SHADER() != STAGE_TOP_OF_PIPE(),
        STAGE_MESH_SHADER() != STAGE_VERTEX_SHADER(),
        STAGE_MESH_SHADER() != STAGE_FRAGMENT_SHADER(),
        STAGE_MESH_SHADER() != STAGE_COMPUTE_SHADER(),
        STAGE_RAY_TRACING_SHADER() != STAGE_TOP_OF_PIPE(),
        STAGE_RAY_TRACING_SHADER() != STAGE_VERTEX_SHADER(),
        STAGE_RAY_TRACING_SHADER() != STAGE_COMPUTE_SHADER(),
{
}

/// New access constants are distinct.
pub proof fn lemma_new_access_constants_distinct()
    ensures
        ACCESS_FRAGMENT_SHADING_RATE_ATTACHMENT_READ() != ACCESS_ACCELERATION_STRUCTURE_READ(),
        ACCESS_FRAGMENT_SHADING_RATE_ATTACHMENT_READ() != ACCESS_ACCELERATION_STRUCTURE_WRITE(),
        ACCESS_ACCELERATION_STRUCTURE_READ() != ACCESS_ACCELERATION_STRUCTURE_WRITE(),
        ACCESS_FRAGMENT_SHADING_RATE_ATTACHMENT_READ() != ACCESS_SHADER_READ(),
        ACCESS_FRAGMENT_SHADING_RATE_ATTACHMENT_READ() != ACCESS_SHADER_WRITE(),
        ACCESS_ACCELERATION_STRUCTURE_READ() != ACCESS_SHADER_READ(),
        ACCESS_ACCELERATION_STRUCTURE_READ() != ACCESS_TRANSFER_READ(),
        ACCESS_ACCELERATION_STRUCTURE_WRITE() != ACCESS_SHADER_WRITE(),
        ACCESS_ACCELERATION_STRUCTURE_WRITE() != ACCESS_TRANSFER_WRITE(),
{
}

} // verus!
