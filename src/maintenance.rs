use vstd::prelude::*;
use crate::flags::*;
use crate::dynamic_rendering::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// Extended pipeline create flags (VK_KHR_maintenance5).
pub struct PipelineCreateFlags2 {
    pub flags: Set<nat>,
}

/// Extended buffer usage flags (VK_KHR_maintenance5).
pub struct BufferUsageFlags2 {
    pub flags: Set<nat>,
}

/// Rendering area info extracted from dynamic rendering (maintenance5).
pub struct RenderingAreaInfo {
    pub view_mask: nat,
    pub color_attachment_count: nat,
    pub color_attachment_formats: Seq<nat>,
    pub depth_attachment_format: Option<nat>,
    pub stencil_attachment_format: Option<nat>,
}

/// Pipeline buffer device address info (maintenance5).
pub struct PipelineBufferAddressInfo {
    pub address: nat,
    pub range: nat,
}

// ── Spec Constants ──────────────────────────────────────────────────────

pub open spec fn PIPELINE_CREATE_2_DISABLE_OPTIMIZATION() -> nat { 0 }
pub open spec fn PIPELINE_CREATE_2_ALLOW_DERIVATIVES() -> nat { 1 }
pub open spec fn PIPELINE_CREATE_2_DERIVATIVE() -> nat { 2 }
pub open spec fn PIPELINE_CREATE_2_RETAIN_LINK_TIME_OPTIMIZATION() -> nat { 3 }
pub open spec fn PIPELINE_CREATE_2_LINK_TIME_OPTIMIZATION() -> nat { 4 }

pub open spec fn BUFFER_USAGE_2_TRANSFER_SRC() -> nat { 0 }
pub open spec fn BUFFER_USAGE_2_TRANSFER_DST() -> nat { 1 }
pub open spec fn BUFFER_USAGE_2_UNIFORM_TEXEL_BUFFER() -> nat { 2 }
pub open spec fn BUFFER_USAGE_2_STORAGE_TEXEL_BUFFER() -> nat { 3 }
pub open spec fn BUFFER_USAGE_2_PUSH_DESCRIPTORS() -> nat { 4 }

// ── Spec Functions ──────────────────────────────────────────────────────

/// Pipeline create flags are well-formed: DISABLE_OPTIMIZATION excludes ALLOW_DERIVATIVES.
pub open spec fn pipeline_create_flags_well_formed(flags: PipelineCreateFlags2) -> bool {
    !(flags.flags.contains(PIPELINE_CREATE_2_DISABLE_OPTIMIZATION())
      && flags.flags.contains(PIPELINE_CREATE_2_ALLOW_DERIVATIVES()))
}

/// Buffer usage flags2 are well-formed: non-empty.
pub open spec fn buffer_usage_flags2_well_formed(flags: BufferUsageFlags2) -> bool {
    flags.flags.len() > 0
}

/// Rendering area info is well-formed.
pub open spec fn rendering_area_well_formed(info: RenderingAreaInfo) -> bool {
    info.color_attachment_count == info.color_attachment_formats.len()
    && (forall|i: int| 0 <= i < info.color_attachment_formats.len()
        ==> info.color_attachment_formats[i] > 0)
}

/// Pipeline buffer address is valid: range > 0, no overflow.
pub open spec fn pipeline_buffer_address_valid(info: PipelineBufferAddressInfo) -> bool {
    info.range > 0
    && info.address + info.range > info.address  // no overflow
}

/// DISABLE_OPTIMIZATION implies no ALLOW_DERIVATIVES.
pub open spec fn disable_optimization_no_derivatives(flags: PipelineCreateFlags2) -> bool {
    flags.flags.contains(PIPELINE_CREATE_2_DISABLE_OPTIMIZATION())
    ==> !flags.flags.contains(PIPELINE_CREATE_2_ALLOW_DERIVATIVES())
}

/// LTO flags are mutually consistent.
pub open spec fn link_time_optimization_valid(flags: PipelineCreateFlags2) -> bool {
    // RETAIN_LTO and LTO can coexist (retain is for libraries, LTO is for final link)
    true
}

/// Buffer usage flags2 contain at least one transfer usage.
pub open spec fn buffer_usage2_contains_transfer(flags: BufferUsageFlags2) -> bool {
    flags.flags.contains(BUFFER_USAGE_2_TRANSFER_SRC())
    || flags.flags.contains(BUFFER_USAGE_2_TRANSFER_DST())
}

/// Number of color attachments in a rendering area.
pub open spec fn rendering_area_color_count(area: RenderingAreaInfo) -> nat {
    area.color_attachment_count
}

/// Extract rendering area info from dynamic rendering info.
pub open spec fn get_rendering_area_info(
    info: DynamicRenderingInfo,
) -> RenderingAreaInfo {
    RenderingAreaInfo {
        view_mask: 0,
        color_attachment_count: info.color_attachments.len(),
        color_attachment_formats: Seq::new(
            info.color_attachments.len(),
            |i: int| 1nat, // placeholder format id (non-zero = valid format)
        ),
        depth_attachment_format: if info.depth_attachment.is_some() { Some(1nat) } else { None },
        stencil_attachment_format: if info.stencil_attachment.is_some() { Some(1nat) } else { None },
    }
}

/// Two buffer address ranges overlap.
pub open spec fn buffer_address_overlap(
    a: PipelineBufferAddressInfo,
    b: PipelineBufferAddressInfo,
) -> bool {
    a.address < b.address + b.range && b.address < a.address + a.range
}

/// Two buffer address ranges are disjoint.
pub open spec fn buffer_address_disjoint(
    a: PipelineBufferAddressInfo,
    b: PipelineBufferAddressInfo,
) -> bool {
    !buffer_address_overlap(a, b)
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// Well-formed create flags satisfy disable_optimization_no_derivatives.
pub proof fn lemma_flags_well_formed_nonempty(flags: PipelineCreateFlags2)
    requires pipeline_create_flags_well_formed(flags),
    ensures disable_optimization_no_derivatives(flags),
{
}

/// DISABLE_OPTIMIZATION + ALLOW_DERIVATIVES is invalid.
pub proof fn lemma_disable_optimization_exclusive(flags: PipelineCreateFlags2)
    requires
        flags.flags.contains(PIPELINE_CREATE_2_DISABLE_OPTIMIZATION()),
        flags.flags.contains(PIPELINE_CREATE_2_ALLOW_DERIVATIVES()),
    ensures !pipeline_create_flags_well_formed(flags),
{
}

/// Well-formed buffer usage2 is non-empty.
pub proof fn lemma_buffer_usage2_nonempty(flags: BufferUsageFlags2)
    requires buffer_usage_flags2_well_formed(flags),
    ensures flags.flags.len() > 0,
{
}

/// Well-formed rendering area has matching format count.
pub proof fn lemma_rendering_area_formats_match_count(area: RenderingAreaInfo)
    requires rendering_area_well_formed(area),
    ensures area.color_attachment_formats.len() == area.color_attachment_count,
{
}

/// Valid pipeline buffer address has positive range.
pub proof fn lemma_pipeline_buffer_address_positive_range(info: PipelineBufferAddressInfo)
    requires pipeline_buffer_address_valid(info),
    ensures info.range > 0,
{
}

/// Buffer address disjoint is symmetric.
pub proof fn lemma_buffer_address_disjoint_symmetric(
    a: PipelineBufferAddressInfo,
    b: PipelineBufferAddressInfo,
)
    ensures buffer_address_disjoint(a, b) == buffer_address_disjoint(b, a),
{
    // overlap(a,b) ↔ overlap(b,a)
    assert(buffer_address_overlap(a, b) == buffer_address_overlap(b, a));
}

/// Overlap iff not disjoint.
pub proof fn lemma_buffer_address_overlap_not_disjoint(
    a: PipelineBufferAddressInfo,
    b: PipelineBufferAddressInfo,
)
    ensures buffer_address_overlap(a, b) <==> !buffer_address_disjoint(a, b),
{
}

/// LTO flags are always consistent (retain + LTO are compatible).
pub proof fn lemma_lto_flags_consistent(flags: PipelineCreateFlags2)
    ensures link_time_optimization_valid(flags),
{
}

/// get_rendering_area_info preserves color attachment count.
pub proof fn lemma_rendering_area_from_dynamic(info: DynamicRenderingInfo)
    ensures
        get_rendering_area_info(info).color_attachment_count
            == info.color_attachments.len(),
{
}

/// Zero color attachments means empty format list.
pub proof fn lemma_zero_color_count_no_formats(area: RenderingAreaInfo)
    requires
        rendering_area_well_formed(area),
        area.color_attachment_count == 0,
    ensures area.color_attachment_formats.len() == 0,
{
}

} // verus!
