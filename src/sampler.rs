use vstd::prelude::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// Texture filter mode.
pub enum Filter {
    Nearest,
    Linear,
}

/// Texture address mode (wrap behavior).
pub enum AddressMode {
    Repeat,
    MirroredRepeat,
    ClampToEdge,
    ClampToBorder,
}

/// Mipmap filtering mode.
pub enum MipmapMode {
    Nearest,
    Linear,
}

/// Ghost state for a Vulkan sampler (VkSampler).
pub struct SamplerState {
    pub id: nat,
    pub mag_filter: Filter,
    pub min_filter: Filter,
    pub mipmap_mode: MipmapMode,
    pub address_mode_u: AddressMode,
    pub address_mode_v: AddressMode,
    pub address_mode_w: AddressMode,
    pub anisotropy_enable: bool,
    pub max_anisotropy: nat,
    pub compare_enable: bool,
    /// Whether the sampler uses unnormalized coordinates [0, width) instead of [0, 1).
    pub unnormalized_coordinates: bool,
    pub alive: bool,
}

// ── Ghost Destroy ──────────────────────────────────────────────────────

/// Ghost update: destroy a sampler.
pub open spec fn destroy_sampler_ghost(sampler: SamplerState) -> SamplerState {
    SamplerState {
        alive: false,
        ..sampler
    }
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// A sampler is well-formed per Vulkan spec constraints.
/// Unnormalized coordinates impose several restrictions.
pub open spec fn sampler_well_formed(sampler: SamplerState) -> bool {
    sampler.alive
    && (sampler.unnormalized_coordinates ==> (
        // Must use Nearest filter
        sampler.mag_filter == Filter::Nearest
        && sampler.min_filter == Filter::Nearest
        // Must use Nearest mipmap mode
        && sampler.mipmap_mode == MipmapMode::Nearest
        // Must use ClampToEdge or ClampToBorder
        && address_mode_is_clamp(sampler.address_mode_u)
        && address_mode_is_clamp(sampler.address_mode_v)
        // No anisotropy
        && !sampler.anisotropy_enable
        // No comparison
        && !sampler.compare_enable
    ))
    // Anisotropy max must be >= 1 if enabled
    && (sampler.anisotropy_enable ==> sampler.max_anisotropy >= 1)
}

/// Whether an address mode is a clamping mode.
pub open spec fn address_mode_is_clamp(mode: AddressMode) -> bool {
    mode == AddressMode::ClampToEdge || mode == AddressMode::ClampToBorder
}

/// A sampler is compatible with a 1D image (unnormalized coordinates
/// allowed only for 1D/2D non-array images).
pub open spec fn sampler_dimension_compatible(
    sampler: SamplerState,
    image_dimensions: nat,  // 1, 2, or 3
    is_array: bool,
) -> bool {
    // Unnormalized coordinates: only 1D or 2D, no arrays
    sampler.unnormalized_coordinates ==> (
        (image_dimensions == 1 || image_dimensions == 2) && !is_array
    )
}

/// A comparison sampler requires a depth format image.
pub open spec fn compare_sampler_format_valid(
    sampler: SamplerState,
    is_depth_format: bool,
) -> bool {
    sampler.compare_enable ==> is_depth_format
}

/// Full sampler-image compatibility.
pub open spec fn sampler_image_compatible(
    sampler: SamplerState,
    image_dimensions: nat,
    is_array: bool,
    is_depth_format: bool,
) -> bool {
    sampler_well_formed(sampler)
    && sampler_dimension_compatible(sampler, image_dimensions, is_array)
    && compare_sampler_format_valid(sampler, is_depth_format)
}

/// A default normalized sampler with no special features.
pub open spec fn default_sampler(id: nat) -> SamplerState {
    SamplerState {
        id,
        mag_filter: Filter::Linear,
        min_filter: Filter::Linear,
        mipmap_mode: MipmapMode::Linear,
        address_mode_u: AddressMode::Repeat,
        address_mode_v: AddressMode::Repeat,
        address_mode_w: AddressMode::Repeat,
        anisotropy_enable: false,
        max_anisotropy: 0,
        compare_enable: false,
        unnormalized_coordinates: false,
        alive: true,
    }
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// The default sampler is well-formed.
pub proof fn lemma_default_sampler_well_formed(id: nat)
    ensures sampler_well_formed(default_sampler(id)),
{
}

/// The default sampler is compatible with any non-depth image.
pub proof fn lemma_default_sampler_compatible(
    id: nat,
    image_dimensions: nat,
    is_array: bool,
)
    ensures
        sampler_image_compatible(default_sampler(id), image_dimensions, is_array, false),
{
}

/// A nearest sampler with ClampToEdge is well-formed for unnormalized coordinates.
pub proof fn lemma_nearest_clamp_unnormalized_valid(id: nat)
    ensures sampler_well_formed(SamplerState {
        id,
        mag_filter: Filter::Nearest,
        min_filter: Filter::Nearest,
        mipmap_mode: MipmapMode::Nearest,
        address_mode_u: AddressMode::ClampToEdge,
        address_mode_v: AddressMode::ClampToEdge,
        address_mode_w: AddressMode::ClampToEdge,
        anisotropy_enable: false,
        max_anisotropy: 0,
        compare_enable: false,
        unnormalized_coordinates: true,
        alive: true,
    }),
{
}

/// ClampToEdge is a clamping mode.
pub proof fn lemma_clamp_to_edge_is_clamp()
    ensures address_mode_is_clamp(AddressMode::ClampToEdge),
{
}

/// Repeat is NOT a clamping mode.
pub proof fn lemma_repeat_not_clamp()
    ensures !address_mode_is_clamp(AddressMode::Repeat),
{
}

/// Well-formedness implies alive.
pub proof fn lemma_well_formed_implies_alive(sampler: SamplerState)
    requires sampler_well_formed(sampler),
    ensures sampler.alive,
{
}

/// After destroying, a sampler is not alive.
pub proof fn lemma_destroy_sampler_not_alive(sampler: SamplerState)
    ensures !destroy_sampler_ghost(sampler).alive,
{
}

/// Destroying a sampler preserves its id.
pub proof fn lemma_destroy_sampler_preserves_id(sampler: SamplerState)
    ensures destroy_sampler_ghost(sampler).id == sampler.id,
{
}

} // verus!
