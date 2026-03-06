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

} // verus!
