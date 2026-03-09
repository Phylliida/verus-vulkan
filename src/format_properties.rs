use vstd::prelude::*;
use crate::descriptor::DescriptorType;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// Format feature flags: what operations a format supports.
pub struct FormatFeatureFlags {
    pub sampled_image: bool,
    pub storage_image: bool,
    pub color_attachment: bool,
    pub color_attachment_blend: bool,
    pub depth_stencil_attachment: bool,
    pub blit_src: bool,
    pub blit_dst: bool,
    pub transfer_src: bool,
    pub transfer_dst: bool,
    pub vertex_buffer: bool,
}

/// Format properties for a specific format on the current device.
pub struct FormatProperties {
    pub format_id: nat,
    /// Features supported for linear tiling.
    pub linear_tiling: FormatFeatureFlags,
    /// Features supported for optimal tiling.
    pub optimal_tiling: FormatFeatureFlags,
    /// Features supported for buffer usage.
    pub buffer_features: FormatFeatureFlags,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// A format supports being used as a sampled image (in a shader).
pub open spec fn format_supports_sampling(props: FormatProperties) -> bool {
    props.optimal_tiling.sampled_image
}

/// A format supports being used as a color attachment.
pub open spec fn format_supports_color_attachment(props: FormatProperties) -> bool {
    props.optimal_tiling.color_attachment
}

/// A format supports blending as a color attachment.
pub open spec fn format_supports_blend(props: FormatProperties) -> bool {
    props.optimal_tiling.color_attachment_blend
}

/// A format supports being used as a depth/stencil attachment.
pub open spec fn format_supports_depth_stencil(props: FormatProperties) -> bool {
    props.optimal_tiling.depth_stencil_attachment
}

/// A format supports being a blit source.
pub open spec fn format_supports_blit_src(props: FormatProperties) -> bool {
    props.optimal_tiling.blit_src
}

/// A format supports being a blit destination.
pub open spec fn format_supports_blit_dst(props: FormatProperties) -> bool {
    props.optimal_tiling.blit_dst
}

/// A format supports being used as a vertex buffer attribute.
pub open spec fn format_supports_vertex_buffer(props: FormatProperties) -> bool {
    props.buffer_features.vertex_buffer
}

/// A format is usable for a given attachment role in a render pass.
pub open spec fn format_valid_for_attachment(
    props: FormatProperties,
    is_color: bool,
    is_depth: bool,
    blend_enabled: bool,
) -> bool {
    (is_color ==> format_supports_color_attachment(props))
    && (is_color && blend_enabled ==> format_supports_blend(props))
    && (is_depth ==> format_supports_depth_stencil(props))
}

/// A format is usable for transfer operations.
pub open spec fn format_supports_transfer(props: FormatProperties) -> bool {
    props.optimal_tiling.transfer_src && props.optimal_tiling.transfer_dst
}

/// All format properties are consistent (blend requires color attachment).
pub open spec fn format_properties_consistent(props: FormatProperties) -> bool {
    // Blend requires color attachment support
    (props.optimal_tiling.color_attachment_blend
        ==> props.optimal_tiling.color_attachment)
    && (props.linear_tiling.color_attachment_blend
        ==> props.linear_tiling.color_attachment)
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// A format that supports blending also supports color attachment.
pub proof fn lemma_blend_implies_color(props: FormatProperties)
    requires format_properties_consistent(props),
    ensures
        format_supports_blend(props) ==> format_supports_color_attachment(props),
{
}

/// A format valid for depth attachment supports depth/stencil.
pub proof fn lemma_depth_valid_implies_support(
    props: FormatProperties,
)
    requires format_valid_for_attachment(props, false, true, false),
    ensures format_supports_depth_stencil(props),
{
}

/// A format valid for color attachment with blend supports both.
pub proof fn lemma_color_blend_valid(
    props: FormatProperties,
)
    requires format_valid_for_attachment(props, true, false, true),
    ensures
        format_supports_color_attachment(props),
        format_supports_blend(props),
{
}

/// A format that doesn't support color attachment is not valid for color.
pub proof fn lemma_no_color_support_invalid(
    props: FormatProperties,
)
    requires !format_supports_color_attachment(props),
    ensures !format_valid_for_attachment(props, true, false, false),
{
}

/// Transfer support implies both src and dst.
pub proof fn lemma_transfer_both_directions(props: FormatProperties)
    requires format_supports_transfer(props),
    ensures
        props.optimal_tiling.transfer_src,
        props.optimal_tiling.transfer_dst,
{
}

/// A format valid for color (without blend) supports color attachment.
pub proof fn lemma_color_valid_implies_support(props: FormatProperties)
    requires format_valid_for_attachment(props, true, false, false),
    ensures format_supports_color_attachment(props),
{
}

/// A format valid for both color and depth supports both.
pub proof fn lemma_color_depth_valid(props: FormatProperties)
    requires format_valid_for_attachment(props, true, true, false),
    ensures
        format_supports_color_attachment(props),
        format_supports_depth_stencil(props),
{
}

/// A pure depth format (no color) is valid iff it supports depth/stencil.
pub proof fn lemma_pure_depth_format(props: FormatProperties)
    ensures
        format_valid_for_attachment(props, false, true, false)
        == format_supports_depth_stencil(props),
{
}

/// A format with neither color nor depth role is always valid.
pub proof fn lemma_no_role_always_valid(props: FormatProperties)
    ensures format_valid_for_attachment(props, false, false, false),
{
}

/// Sampling support is independent of attachment support.
pub proof fn lemma_sampling_independent_of_attachment(
    props: FormatProperties, is_color: bool, is_depth: bool, blend: bool,
)
    requires
        format_valid_for_attachment(props, is_color, is_depth, blend),
        format_supports_sampling(props),
    ensures
        format_valid_for_attachment(props, is_color, is_depth, blend),
{
}

// ── Tiling-Aware Feature Lookups ─────────────────────────────────────────

/// Returns the feature flags appropriate for the given tiling mode.
/// tiling == 0 → optimal_tiling; tiling == 1 → linear_tiling.
pub open spec fn format_features_for_tiling(
    props: FormatProperties,
    tiling: nat,
) -> FormatFeatureFlags {
    if tiling == 0 { props.optimal_tiling } else { props.linear_tiling }
}

/// A format supports sampling for the given tiling mode.
pub open spec fn format_supports_sampling_for_tiling(
    props: FormatProperties,
    tiling: nat,
) -> bool {
    format_features_for_tiling(props, tiling).sampled_image
}

/// A format supports color attachment for the given tiling mode.
pub open spec fn format_supports_color_attachment_for_tiling(
    props: FormatProperties,
    tiling: nat,
) -> bool {
    format_features_for_tiling(props, tiling).color_attachment
}

/// A format supports depth/stencil attachment for the given tiling mode.
pub open spec fn format_supports_depth_stencil_for_tiling(
    props: FormatProperties,
    tiling: nat,
) -> bool {
    format_features_for_tiling(props, tiling).depth_stencil_attachment
}

/// A format supports storage image for the given tiling mode.
pub open spec fn format_supports_storage_for_tiling(
    props: FormatProperties,
    tiling: nat,
) -> bool {
    format_features_for_tiling(props, tiling).storage_image
}

/// Optimal tiling (tiling==0) gives the same results as the existing functions.
pub proof fn lemma_optimal_tiling_matches_existing(props: FormatProperties)
    ensures
        format_supports_sampling_for_tiling(props, 0) == format_supports_sampling(props),
        format_supports_color_attachment_for_tiling(props, 0) == format_supports_color_attachment(props),
        format_supports_depth_stencil_for_tiling(props, 0) == format_supports_depth_stencil(props),
        format_supports_storage_for_tiling(props, 0) == props.optimal_tiling.storage_image,
{
}

/// Linear tiling (tiling==1) uses the linear_tiling field.
pub proof fn lemma_linear_tiling_uses_linear_features(props: FormatProperties)
    ensures
        format_supports_sampling_for_tiling(props, 1) == props.linear_tiling.sampled_image,
        format_supports_color_attachment_for_tiling(props, 1) == props.linear_tiling.color_attachment,
        format_supports_depth_stencil_for_tiling(props, 1) == props.linear_tiling.depth_stencil_attachment,
        format_supports_storage_for_tiling(props, 1) == props.linear_tiling.storage_image,
{
}

// ── Format + Descriptor Type Validation ─────────────────────────────────

/// Whether a format's features are adequate for a given descriptor type.
/// SampledImage and CombinedImageSampler need sampling support;
/// StorageImage needs storage support; buffer types pass trivially.
pub open spec fn format_valid_for_descriptor_type(
    props: FormatProperties,
    desc_type: DescriptorType,
) -> bool {
    match desc_type {
        DescriptorType::SampledImage => format_supports_sampling(props),
        DescriptorType::CombinedImageSampler => format_supports_sampling(props),
        DescriptorType::StorageImage => props.optimal_tiling.storage_image,
        DescriptorType::UniformBuffer => true,
        DescriptorType::StorageBuffer => true,
        DescriptorType::UniformBufferDynamic => true,
        DescriptorType::StorageBufferDynamic => true,
        DescriptorType::InputAttachment => true,
    }
}

/// Buffer descriptor types are always format-valid (no image features needed).
pub proof fn lemma_buffer_type_format_valid(props: FormatProperties)
    ensures
        format_valid_for_descriptor_type(props, DescriptorType::UniformBuffer),
        format_valid_for_descriptor_type(props, DescriptorType::StorageBuffer),
        format_valid_for_descriptor_type(props, DescriptorType::InputAttachment),
{
}

/// A format with sampling support is valid for SampledImage descriptors.
pub proof fn lemma_sampling_valid_for_sampled(props: FormatProperties)
    requires format_supports_sampling(props),
    ensures format_valid_for_descriptor_type(props, DescriptorType::SampledImage),
{
}

/// A format with sampling support is valid for CombinedImageSampler descriptors.
pub proof fn lemma_sampling_valid_for_combined(props: FormatProperties)
    requires format_supports_sampling(props),
    ensures format_valid_for_descriptor_type(props, DescriptorType::CombinedImageSampler),
{
}

} // verus!
