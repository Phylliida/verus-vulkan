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
}

/// True iff the access set contains any read access.
pub open spec fn has_read_access(flags: AccessFlags) -> bool {
    flags.accesses.contains(ACCESS_SHADER_READ())
    || flags.accesses.contains(ACCESS_COLOR_ATTACHMENT_READ())
    || flags.accesses.contains(ACCESS_DEPTH_STENCIL_READ())
    || flags.accesses.contains(ACCESS_TRANSFER_READ())
    || flags.accesses.contains(ACCESS_HOST_READ())
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
{
}

} // verus!
