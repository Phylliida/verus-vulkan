use vstd::prelude::*;

verus! {

//  ── Types ───────────────────────────────────────────────────────────────

///  Subgroup (warp/wavefront) feature categories.
pub enum SubgroupFeature {
    Basic,
    Vote,
    Arithmetic,
    Ballot,
    Shuffle,
    ShuffleRelative,
    Clustered,
    Quad,
}

///  Physical device subgroup properties.
pub struct SubgroupProperties {
    ///  Number of invocations in a subgroup (typically 32 or 64).
    pub subgroup_size: nat,
    ///  Set of pipeline stages where subgroup operations are supported.
    pub supported_stages: Set<nat>,
    ///  Set of supported subgroup features.
    pub supported_operations: Set<SubgroupFeature>,
    ///  Whether quad operations are available in all stages.
    pub quad_in_all_stages: bool,
}

//  ── Spec Functions ──────────────────────────────────────────────────────

///  Subgroup properties are well-formed.
pub open spec fn subgroup_properties_well_formed(props: SubgroupProperties) -> bool {
    props.subgroup_size > 0
    && is_power_of_two(props.subgroup_size)
    && props.supported_operations.contains(SubgroupFeature::Basic)
}

///  Whether a specific subgroup feature is supported.
pub open spec fn subgroup_supports_feature(
    props: SubgroupProperties,
    feature: SubgroupFeature,
) -> bool {
    props.supported_operations.contains(feature)
}

///  Whether a subgroup feature is available at a given pipeline stage.
pub open spec fn subgroup_feature_available_at_stage(
    props: SubgroupProperties,
    feature: SubgroupFeature,
    stage: nat,
) -> bool {
    props.supported_operations.contains(feature)
    && props.supported_stages.contains(stage)
}

///  Whether n is a power of two.
pub open spec fn is_power_of_two(n: nat) -> bool
    decreases n,
{
    if n == 0 {
        false
    } else if n == 1 {
        true
    } else {
        n % 2 == 0 && is_power_of_two(n / 2)
    }
}

///  A shader's subgroup usage is valid with respect to the device properties.
pub open spec fn shader_uses_subgroup_valid(
    props: SubgroupProperties,
    used_features: Set<SubgroupFeature>,
    stage: nat,
) -> bool {
    used_features.subset_of(props.supported_operations)
    && props.supported_stages.contains(stage)
}

//  ── Lemmas ──────────────────────────────────────────────────────────────

///  Basic subgroup feature is always supported in well-formed properties.
pub proof fn lemma_basic_always_supported(props: SubgroupProperties)
    requires subgroup_properties_well_formed(props),
    ensures subgroup_supports_feature(props, SubgroupFeature::Basic),
{
}

///  A power of two is at least 1.
pub proof fn lemma_power_of_two_positive(n: nat)
    requires is_power_of_two(n),
    ensures n >= 1,
    decreases n,
{
    if n > 1 {
        lemma_power_of_two_positive(n / 2);
    }
}

///  Feature availability at a stage implies the feature is supported.
pub proof fn lemma_available_implies_supported(
    props: SubgroupProperties,
    feature: SubgroupFeature,
    stage: nat,
)
    requires subgroup_feature_available_at_stage(props, feature, stage),
    ensures subgroup_supports_feature(props, feature),
{
}

///  Valid shader subgroup usage implies each used feature is supported.
pub proof fn lemma_valid_usage_implies_features_supported(
    props: SubgroupProperties,
    used_features: Set<SubgroupFeature>,
    stage: nat,
)
    requires shader_uses_subgroup_valid(props, used_features, stage),
    ensures used_features.subset_of(props.supported_operations),
{
}

///  1 is a power of two.
pub proof fn lemma_one_is_power_of_two()
    ensures is_power_of_two(1nat),
{
}

} //  verus!
