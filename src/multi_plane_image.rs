use vstd::prelude::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// Image plane aspects for multi-planar formats.
pub enum PlaneAspect {
    Plane0,
    Plane1,
    Plane2,
}

/// Chroma sample location relative to luma samples.
pub enum ChromaLocation {
    CositedEven,
    Midpoint,
}

/// Range of YCbCr values.
pub enum SamplerYcbcrRange {
    ItuFull,
    ItuNarrow,
}

/// YCbCr model conversion mode.
pub enum SamplerYcbcrModelConversion {
    RgbIdentity,
    YcbcrIdentity,
    Ycbcr709,
    Ycbcr601,
    Ycbcr2020,
}

/// State of a YCbCr conversion object.
pub struct YcbcrConversionState {
    pub id: nat,
    pub format: nat,
    pub model: SamplerYcbcrModelConversion,
    pub range: SamplerYcbcrRange,
    pub x_chroma_offset: ChromaLocation,
    pub y_chroma_offset: ChromaLocation,
    pub force_explicit_reconstruction: bool,
    pub alive: bool,
}

/// Info about a multi-plane image format.
pub struct MultiPlaneImageInfo {
    pub format: nat,
    pub plane_count: nat,
    pub plane_widths: Seq<nat>,
    pub plane_heights: Seq<nat>,
    pub plane_aspects: Seq<PlaneAspect>,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// A YCbCr conversion object is well-formed.
pub open spec fn ycbcr_conversion_well_formed(state: YcbcrConversionState) -> bool {
    state.alive
}

/// Create a fresh YCbCr conversion.
pub open spec fn create_ycbcr_conversion(
    id: nat,
    format: nat,
    model: SamplerYcbcrModelConversion,
    range: SamplerYcbcrRange,
    x_chroma: ChromaLocation,
    y_chroma: ChromaLocation,
) -> YcbcrConversionState {
    YcbcrConversionState {
        id,
        format,
        model,
        range,
        x_chroma_offset: x_chroma,
        y_chroma_offset: y_chroma,
        force_explicit_reconstruction: false,
        alive: true,
    }
}

/// Ghost update: destroy a YCbCr conversion.
pub open spec fn destroy_ycbcr_conversion(state: YcbcrConversionState) -> YcbcrConversionState {
    YcbcrConversionState {
        alive: false,
        ..state
    }
}

/// Whether a format ID represents a multi-planar format.
/// Uses a set of known multi-planar format IDs.
pub open spec fn format_is_multi_planar(format: nat) -> bool {
    format_plane_count(format) > 1
}

/// Number of planes for a format.
/// Known multi-planar VkFormat values mapped to plane counts.
pub open spec fn format_plane_count(format: nat) -> nat {
    if format >= 1000156000 && format <= 1000156031 {
        if format <= 1000156009 { 2 }
        else if format <= 1000156023 { 2 }
        else { 3 }
    } else {
        1
    }
}

/// Multi-plane image info is well-formed.
pub open spec fn multi_plane_image_well_formed(info: MultiPlaneImageInfo) -> bool {
    info.plane_count > 0
    && info.plane_count <= 3
    && info.plane_widths.len() == info.plane_count
    && info.plane_heights.len() == info.plane_count
    && info.plane_aspects.len() == info.plane_count
    && forall|i: int| 0 <= i < info.plane_count ==>
        #[trigger] info.plane_widths[i] > 0 && info.plane_heights[i] > 0
}

/// Plane dimensions are valid (each plane ≤ base dimensions).
pub open spec fn plane_dimensions_valid(
    info: MultiPlaneImageInfo,
    base_width: nat,
    base_height: nat,
) -> bool {
    forall|i: int| 0 <= i < info.plane_count ==>
        #[trigger] info.plane_widths[i] <= base_width
        && info.plane_heights[i] <= base_height
}

/// A YCbCr sampler is compatible with the conversion's format.
pub open spec fn ycbcr_sampler_compatible(
    conversion: YcbcrConversionState,
    sampler_format: nat,
) -> bool {
    conversion.alive
    && conversion.format == sampler_format
}

// ── Lemmas ──────────────────────────────────────────────────────────────

/// Freshly created YCbCr conversion is alive.
pub proof fn lemma_create_ycbcr_alive(
    id: nat, format: nat, model: SamplerYcbcrModelConversion,
    range: SamplerYcbcrRange, x: ChromaLocation, y: ChromaLocation,
)
    ensures create_ycbcr_conversion(id, format, model, range, x, y).alive,
{
}

/// Destroyed YCbCr conversion is not alive.
pub proof fn lemma_destroy_ycbcr_not_alive(state: YcbcrConversionState)
    ensures !destroy_ycbcr_conversion(state).alive,
{
}

/// A single-plane format has plane_count 1.
pub proof fn lemma_single_plane_count(format: nat)
    requires !format_is_multi_planar(format),
    ensures format_plane_count(format) == 1,
{
}

/// Well-formed multi-plane info has positive plane count.
pub proof fn lemma_well_formed_positive_planes(info: MultiPlaneImageInfo)
    requires multi_plane_image_well_formed(info),
    ensures info.plane_count > 0,
{
}

/// Plane dimensions valid implies each plane width ≤ base.
pub proof fn lemma_plane_width_bounded(
    info: MultiPlaneImageInfo,
    base_width: nat,
    base_height: nat,
    i: int,
)
    requires
        plane_dimensions_valid(info, base_width, base_height),
        0 <= i < info.plane_count,
    ensures
        info.plane_widths[i] <= base_width,
{
}

/// Destroying preserves the id.
pub proof fn lemma_destroy_ycbcr_preserves_id(state: YcbcrConversionState)
    ensures destroy_ycbcr_conversion(state).id == state.id,
{
}

} // verus!
