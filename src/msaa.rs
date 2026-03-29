use vstd::prelude::*;

verus! {

//  ── Types ───────────────────────────────────────────────────────────────

///  Sample count for multisampling.
pub enum SampleCount {
    S1,
    S2,
    S4,
    S8,
    S16,
    S32,
    S64,
}

///  MSAA resolve operation between a multisample source and single-sample destination.
pub struct ResolveOperation {
    ///  Source (multisample) image id.
    pub src_image: nat,
    ///  Destination (single-sample) image id.
    pub dst_image: nat,
    ///  Source sample count.
    pub src_samples: SampleCount,
    ///  Destination must be single-sample.
    pub dst_samples: SampleCount,
}

//  ── Spec Functions ──────────────────────────────────────────────────────

///  Convert sample count to a numeric value.
pub open spec fn sample_count_value(sc: SampleCount) -> nat {
    match sc {
        SampleCount::S1 => 1,
        SampleCount::S2 => 2,
        SampleCount::S4 => 4,
        SampleCount::S8 => 8,
        SampleCount::S16 => 16,
        SampleCount::S32 => 32,
        SampleCount::S64 => 64,
    }
}

///  Sample count is multisampled (more than 1).
pub open spec fn is_multisampled(sc: SampleCount) -> bool {
    sample_count_value(sc) > 1
}

///  A resolve operation is valid: source is multisampled, destination is single-sample.
pub open spec fn resolve_valid(op: ResolveOperation) -> bool {
    is_multisampled(op.src_samples)
    && op.dst_samples == SampleCount::S1
    && op.src_image != op.dst_image
}

///  Pipeline sample count matches the render pass attachment's sample count.
pub open spec fn pipeline_sample_count_matches(
    pipeline_samples: SampleCount,
    attachment_samples: SampleCount,
) -> bool {
    pipeline_samples == attachment_samples
}

///  Sample count is a power of two (always true for valid SampleCount values).
pub open spec fn sample_count_is_power_of_two(sc: SampleCount) -> bool {
    let v = sample_count_value(sc);
    v == 1 || v == 2 || v == 4 || v == 8 || v == 16 || v == 32 || v == 64
}

///  A render pass attachment resolve is well-formed: if there is a resolve
///  attachment, the color attachment must be multisampled and the resolve
///  attachment must be single-sample.
pub open spec fn attachment_resolve_well_formed(
    color_samples: SampleCount,
    has_resolve: bool,
    resolve_samples: SampleCount,
) -> bool {
    has_resolve ==> (
        is_multisampled(color_samples)
        && resolve_samples == SampleCount::S1
    )
}

///  All sample counts in a pipeline match the render pass.
pub open spec fn all_sample_counts_match(
    pipeline_samples: SampleCount,
    color_samples: Seq<SampleCount>,
    depth_samples: Option<SampleCount>,
) -> bool {
    //  All color attachments must match
    (forall|i: int| 0 <= i < color_samples.len()
        ==> (#[trigger] color_samples[i]) == pipeline_samples)
    //  Depth attachment must match if present
    && (match depth_samples {
        Some(ds) => ds == pipeline_samples,
        None => true,
    })
}

//  ── Proofs ──────────────────────────────────────────────────────────────

///  Every sample count value is a power of two.
pub proof fn lemma_sample_count_power_of_two(sc: SampleCount)
    ensures sample_count_is_power_of_two(sc),
{
}

///  S1 is not multisampled.
pub proof fn lemma_s1_not_multisampled()
    ensures !is_multisampled(SampleCount::S1),
{
}

///  S4 is multisampled.
pub proof fn lemma_s4_multisampled()
    ensures is_multisampled(SampleCount::S4),
{
}

///  A resolve from S4 to S1 is valid.
pub proof fn lemma_s4_to_s1_resolve_valid(src: nat, dst: nat)
    requires src != dst,
    ensures
        resolve_valid(ResolveOperation {
            src_image: src,
            dst_image: dst,
            src_samples: SampleCount::S4,
            dst_samples: SampleCount::S1,
        }),
{
}

///  Resolve is not valid if source is single-sample.
pub proof fn lemma_s1_source_resolve_invalid(src: nat, dst: nat)
    ensures
        !resolve_valid(ResolveOperation {
            src_image: src,
            dst_image: dst,
            src_samples: SampleCount::S1,
            dst_samples: SampleCount::S1,
        }),
{
}

///  No resolve attachment means any sample count is fine.
pub proof fn lemma_no_resolve_any_samples(color_samples: SampleCount)
    ensures attachment_resolve_well_formed(color_samples, false, SampleCount::S1),
{
}

///  Matching pipeline and attachment sample counts satisfies the requirement.
pub proof fn lemma_matching_samples_valid(sc: SampleCount)
    ensures pipeline_sample_count_matches(sc, sc),
{
}

} //  verus!
