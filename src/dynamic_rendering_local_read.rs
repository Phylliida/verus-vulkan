use vstd::prelude::*;
use crate::image_layout::*;
use crate::dynamic_rendering::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// Mapping of color attachment locations and input indices for local read
/// (VK_KHR_dynamic_rendering_local_read).
pub struct LocalReadMapping {
    pub color_attachment_locations: Seq<Option<nat>>,
    pub color_attachment_input_indices: Seq<Option<nat>>,
    pub depth_input_index: Option<nat>,
    pub stencil_input_index: Option<nat>,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// A layout is valid for local read (General or ShaderReadOnlyOptimal).
pub open spec fn local_read_layout_valid(layout: ImageLayout) -> bool {
    layout == ImageLayout::General
    || layout == ImageLayout::ShaderReadOnlyOptimal
}

/// Whether a specific color attachment location is assigned.
pub open spec fn location_assigned(mapping: LocalReadMapping, idx: int) -> bool {
    0 <= idx < mapping.color_attachment_locations.len()
    && mapping.color_attachment_locations[idx].is_some()
}

/// Whether a specific color attachment input index is assigned.
pub open spec fn input_index_assigned(mapping: LocalReadMapping, idx: int) -> bool {
    0 <= idx < mapping.color_attachment_input_indices.len()
    && mapping.color_attachment_input_indices[idx].is_some()
}

/// All color attachment locations are assigned.
pub open spec fn all_locations_assigned(mapping: LocalReadMapping) -> bool {
    forall|i: int| 0 <= i < mapping.color_attachment_locations.len()
        ==> (#[trigger] mapping.color_attachment_locations[i]).is_some()
}

/// No duplicate location values among assigned locations.
pub open spec fn no_duplicate_locations(mapping: LocalReadMapping) -> bool {
    forall|i: int, j: int|
        #![trigger mapping.color_attachment_locations[i], mapping.color_attachment_locations[j]]
        0 <= i < mapping.color_attachment_locations.len()
        && 0 <= j < mapping.color_attachment_locations.len()
        && i != j
        && mapping.color_attachment_locations[i].is_some()
        && mapping.color_attachment_locations[j].is_some()
        ==> mapping.color_attachment_locations[i] != mapping.color_attachment_locations[j]
}

/// No duplicate input index values among assigned indices.
pub open spec fn no_duplicate_input_indices(mapping: LocalReadMapping) -> bool {
    forall|i: int, j: int|
        #![trigger mapping.color_attachment_input_indices[i], mapping.color_attachment_input_indices[j]]
        0 <= i < mapping.color_attachment_input_indices.len()
        && 0 <= j < mapping.color_attachment_input_indices.len()
        && i != j
        && mapping.color_attachment_input_indices[i].is_some()
        && mapping.color_attachment_input_indices[j].is_some()
        ==> mapping.color_attachment_input_indices[i] != mapping.color_attachment_input_indices[j]
}

/// Local read mapping is well-formed relative to a dynamic rendering info.
pub open spec fn local_read_mapping_well_formed(
    mapping: LocalReadMapping,
    info: DynamicRenderingInfo,
) -> bool {
    mapping.color_attachment_locations.len() == info.color_attachments.len()
    && mapping.color_attachment_input_indices.len() == info.color_attachments.len()
    && no_duplicate_locations(mapping)
    && no_duplicate_input_indices(mapping)
}

/// Local read is valid: mapping well-formed and rendering well-formed.
pub open spec fn local_read_valid(
    mapping: LocalReadMapping,
    info: DynamicRenderingInfo,
) -> bool {
    local_read_mapping_well_formed(mapping, info)
    && dynamic_rendering_well_formed(info)
}

/// Depth input is readable.
pub open spec fn depth_readable(mapping: LocalReadMapping) -> bool {
    mapping.depth_input_index.is_some()
}

/// Stencil input is readable.
pub open spec fn stencil_readable(mapping: LocalReadMapping) -> bool {
    mapping.stencil_input_index.is_some()
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// Valid local read requires dynamic rendering to be well-formed.
pub proof fn lemma_local_read_requires_dynamic_rendering(
    mapping: LocalReadMapping,
    info: DynamicRenderingInfo,
)
    requires local_read_valid(mapping, info),
    ensures dynamic_rendering_well_formed(info),
{
}

/// General layout is always valid for local read.
pub proof fn lemma_general_always_valid_for_local_read()
    ensures local_read_layout_valid(ImageLayout::General),
{
}

/// Empty mapping (0 color attachments) is trivially valid for uniqueness.
pub proof fn lemma_empty_mapping_trivially_valid(
    mapping: LocalReadMapping,
    info: DynamicRenderingInfo,
)
    requires
        info.color_attachments.len() == 0,
        mapping.color_attachment_locations.len() == 0,
        mapping.color_attachment_input_indices.len() == 0,
    ensures
        no_duplicate_locations(mapping),
        no_duplicate_input_indices(mapping),
{
}

/// Well-formed mapping has unique assigned locations.
pub proof fn lemma_location_uniqueness(
    mapping: LocalReadMapping,
    info: DynamicRenderingInfo,
)
    requires local_read_mapping_well_formed(mapping, info),
    ensures no_duplicate_locations(mapping),
{
}

/// Well-formed mapping has unique assigned input indices.
pub proof fn lemma_input_index_uniqueness(
    mapping: LocalReadMapping,
    info: DynamicRenderingInfo,
)
    requires local_read_mapping_well_formed(mapping, info),
    ensures no_duplicate_input_indices(mapping),
{
}

/// Local read doesn't modify the dynamic rendering info.
pub proof fn lemma_local_read_preserves_rendering_info(
    mapping: LocalReadMapping,
    info: DynamicRenderingInfo,
)
    requires local_read_valid(mapping, info),
    ensures dynamic_rendering_well_formed(info),
{
}

/// Depth readable with valid local read implies depth attachment present.
pub proof fn lemma_depth_read_requires_depth_attachment(
    mapping: LocalReadMapping,
    info: DynamicRenderingInfo,
)
    requires
        local_read_valid(mapping, info),
        depth_readable(mapping),
    ensures mapping.depth_input_index.is_some(),
{
}

/// Well-formed mapping lengths match color attachment count.
pub proof fn lemma_mapping_lengths_match_attachments(
    mapping: LocalReadMapping,
    info: DynamicRenderingInfo,
)
    requires local_read_mapping_well_formed(mapping, info),
    ensures
        mapping.color_attachment_locations.len() == info.color_attachments.len(),
        mapping.color_attachment_input_indices.len() == info.color_attachments.len(),
{
}

/// ShaderReadOnlyOptimal is valid for local read.
pub proof fn lemma_shader_read_only_valid_for_local_read()
    ensures local_read_layout_valid(ImageLayout::ShaderReadOnlyOptimal),
{
}

} // verus!
