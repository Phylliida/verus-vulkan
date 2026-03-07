use vstd::prelude::*;
use crate::resource::*;
use crate::image_layout::*;
use crate::render_pass::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// Per-subresource image layout map.
///
/// In Vulkan, each image subresource (mip level × array layer) has an
/// independent layout. The GPU driver physically rearranges memory on
/// layout transitions. Getting this wrong means the GPU reads garbage
/// (tiled vs linear, compressed vs uncompressed).
pub type ImageLayoutMap = Map<ResourceId, ImageLayout>;

/// A layout transition command: resource → new layout.
pub struct LayoutTransition {
    pub resource: ResourceId,
    pub old_layout: ImageLayout,
    pub new_layout: ImageLayout,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// Create an initial layout map: all resources start as Undefined.
pub open spec fn initial_layout_map(resources: Set<ResourceId>) -> ImageLayoutMap {
    Map::new(
        |r: ResourceId| resources.contains(r),
        |r: ResourceId| ImageLayout::Undefined,
    )
}

/// Apply a single layout transition to the map.
pub open spec fn apply_layout_transition(
    map: ImageLayoutMap,
    resource: ResourceId,
    new_layout: ImageLayout,
) -> ImageLayoutMap {
    map.insert(resource, new_layout)
}

/// Apply a sequence of layout transitions.
pub open spec fn apply_transitions(
    map: ImageLayoutMap,
    transitions: Seq<LayoutTransition>,
) -> ImageLayoutMap
    decreases transitions.len(),
{
    if transitions.len() == 0 {
        map
    } else {
        let t = transitions.last();
        apply_layout_transition(
            apply_transitions(map, transitions.drop_last()),
            t.resource,
            t.new_layout,
        )
    }
}

/// Check that a resource has the expected layout in the map.
pub open spec fn has_layout(
    map: ImageLayoutMap,
    resource: ResourceId,
    expected: ImageLayout,
) -> bool {
    map.contains_key(resource) && map[resource] == expected
}

/// All transitions in a sequence are valid (each new_layout is usable).
pub open spec fn all_transitions_valid(transitions: Seq<LayoutTransition>) -> bool {
    forall|i: int| 0 <= i < transitions.len()
        ==> is_usable_layout(#[trigger] transitions[i].new_layout)
}

/// Build the layout transition sequence for render pass begin:
/// each attachment transitions from its current layout to the layout
/// declared in subpass 0.
pub open spec fn render_pass_begin_transitions(
    rp: RenderPassState,
    fb_attachments: Seq<ResourceId>,
) -> Seq<LayoutTransition>
    recommends
        rp.subpasses.len() > 0,
        fb_attachments.len() == rp.attachments.len(),
{
    Seq::new(
        fb_attachments.len(),
        |i: int| {
            let att = rp.attachments[i];
            let sp = rp.subpasses[0];
            LayoutTransition {
                resource: fb_attachments[i],
                old_layout: att.initial_layout,
                new_layout: subpass_attachment_layout(rp, 0, i as nat)
                    .unwrap_or(att.initial_layout),
            }
        },
    )
}

/// Build the layout transition sequence for render pass end:
/// each attachment transitions to its declared final_layout.
pub open spec fn render_pass_end_transitions(
    rp: RenderPassState,
    fb_attachments: Seq<ResourceId>,
) -> Seq<LayoutTransition>
    recommends fb_attachments.len() == rp.attachments.len(),
{
    Seq::new(
        fb_attachments.len(),
        |i: int| LayoutTransition {
            resource: fb_attachments[i],
            old_layout: ImageLayout::Undefined, // don't care for end
            new_layout: rp.attachments[i].final_layout,
        },
    )
}

/// Build the layout transition sequence for next_subpass:
/// attachments transition to the layouts declared in the next subpass.
pub open spec fn next_subpass_transitions(
    rp: RenderPassState,
    fb_attachments: Seq<ResourceId>,
    next_subpass: nat,
) -> Seq<LayoutTransition>
    recommends
        next_subpass < rp.subpasses.len(),
        fb_attachments.len() == rp.attachments.len(),
{
    Seq::new(
        fb_attachments.len(),
        |i: int| {
            let att = rp.attachments[i];
            LayoutTransition {
                resource: fb_attachments[i],
                old_layout: ImageLayout::Undefined,
                new_layout: subpass_attachment_layout(rp, next_subpass, i as nat)
                    .unwrap_or(att.initial_layout),
            }
        },
    )
}

/// Get the layout an attachment should be in during a specific subpass.
/// Returns None if the attachment is not referenced in that subpass.
pub open spec fn subpass_attachment_layout(
    rp: RenderPassState,
    subpass: nat,
    att_idx: nat,
) -> Option<ImageLayout>
    recommends subpass < rp.subpasses.len(),
{
    let sp = rp.subpasses[subpass as int];
    if exists|i: int| 0 <= i < sp.color_attachments.len()
        && sp.color_attachments[i].attachment_index == att_idx
    {
        // Color attachment — pick first matching ref's layout
        Some(sp.color_attachments[
            choose|i: int| 0 <= i < sp.color_attachments.len()
                && sp.color_attachments[i].attachment_index == att_idx
        ].layout)
    } else if sp.depth_attachment.is_some()
        && sp.depth_attachment.unwrap().attachment_index == att_idx
    {
        Some(sp.depth_attachment.unwrap().layout)
    } else if exists|i: int| 0 <= i < sp.input_attachments.len()
        && sp.input_attachments[i].attachment_index == att_idx
    {
        Some(sp.input_attachments[
            choose|i: int| 0 <= i < sp.input_attachments.len()
                && sp.input_attachments[i].attachment_index == att_idx
        ].layout)
    } else {
        None
    }
}

/// All attachments in the layout map match their expected initial layouts,
/// or the render pass declares initial_layout as Undefined (don't care).
pub open spec fn attachments_match_initial_layouts(
    map: ImageLayoutMap,
    rp: RenderPassState,
    fb_attachments: Seq<ResourceId>,
) -> bool
    recommends fb_attachments.len() == rp.attachments.len(),
{
    forall|i: int| #![trigger fb_attachments[i]]
        0 <= i < fb_attachments.len() ==> {
        let att = rp.attachments[i];
        att.initial_layout == ImageLayout::Undefined
        || has_layout(map, fb_attachments[i], att.initial_layout)
    }
}

/// A full render pass lifecycle is layout-valid:
/// the attachments begin in the correct layouts, transition through
/// subpasses, and end in the final layouts.
pub open spec fn render_pass_layout_lifecycle_valid(
    rp: RenderPassState,
) -> bool {
    render_pass_well_formed(rp)
    && (forall|i: int| 0 <= i < rp.attachments.len() ==>
        is_usable_layout(rp.attachments[i].final_layout))
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// Initial layout map maps all resources to Undefined.
pub proof fn lemma_initial_map_all_undefined(
    resources: Set<ResourceId>,
    r: ResourceId,
)
    requires resources.contains(r),
    ensures
        initial_layout_map(resources).contains_key(r),
        initial_layout_map(resources)[r] == ImageLayout::Undefined,
{
}

/// After applying a transition, the target resource has the new layout.
pub proof fn lemma_transition_updates_target(
    map: ImageLayoutMap,
    resource: ResourceId,
    new_layout: ImageLayout,
)
    ensures
        has_layout(
            apply_layout_transition(map, resource, new_layout),
            resource,
            new_layout,
        ),
{
}

/// Applying a transition does not affect other resources.
pub proof fn lemma_transition_preserves_others(
    map: ImageLayoutMap,
    resource: ResourceId,
    new_layout: ImageLayout,
    other: ResourceId,
)
    requires
        other != resource,
        map.contains_key(other),
    ensures
        apply_layout_transition(map, resource, new_layout).contains_key(other),
        apply_layout_transition(map, resource, new_layout)[other] == map[other],
{
}

/// Applying two transitions to different resources commutes.
pub proof fn lemma_transitions_commute(
    map: ImageLayoutMap,
    r1: ResourceId,
    l1: ImageLayout,
    r2: ResourceId,
    l2: ImageLayout,
)
    requires r1 != r2,
    ensures
        apply_layout_transition(
            apply_layout_transition(map, r1, l1), r2, l2
        ) =~=
        apply_layout_transition(
            apply_layout_transition(map, r2, l2), r1, l1
        ),
{
}

/// End transitions produce valid layouts when the render pass is well-formed.
pub proof fn lemma_end_transitions_valid(
    rp: RenderPassState,
    fb_attachments: Seq<ResourceId>,
)
    requires
        render_pass_well_formed(rp),
        fb_attachments.len() == rp.attachments.len(),
    ensures
        all_transitions_valid(render_pass_end_transitions(rp, fb_attachments)),
{
    let transitions = render_pass_end_transitions(rp, fb_attachments);
    assert forall|i: int| 0 <= i < transitions.len()
    implies is_usable_layout(#[trigger] transitions[i].new_layout) by {
        assert(is_usable_layout(rp.attachments[i].final_layout));
    }
}

/// After applying a sequence of transitions with pairwise-distinct targets,
/// every transition's target has the layout specified by that transition.
pub proof fn lemma_distinct_transitions_set_kth(
    map: ImageLayoutMap,
    transitions: Seq<LayoutTransition>,
    k: nat,
)
    requires
        k < transitions.len(),
        // All transition targets are pairwise distinct
        forall|i: int, j: int|
            0 <= i < transitions.len() && 0 <= j < transitions.len() && i != j
            ==> transitions[i].resource != transitions[j].resource,
    ensures
        has_layout(
            apply_transitions(map, transitions),
            transitions[k as int].resource,
            transitions[k as int].new_layout,
        ),
    decreases transitions.len(),
{
    if transitions.len() == 1 {
        // Only one transition, k must be 0
    } else if k == transitions.len() - 1 {
        // k is the last transition — directly from definition
    } else {
        // k < transitions.len() - 1
        let prefix = transitions.drop_last();
        let last = transitions.last();

        // prefix[k] == transitions[k]
        assert(prefix[k as int] == transitions[k as int]);

        // Prefix targets are also pairwise distinct
        assert forall|i: int, j: int|
            0 <= i < prefix.len() && 0 <= j < prefix.len() && i != j
        implies prefix[i].resource != prefix[j].resource by {
            assert(prefix[i] == transitions[i]);
            assert(prefix[j] == transitions[j]);
        }

        // Recurse on prefix (shorter)
        lemma_distinct_transitions_set_kth(map, prefix, k);

        // The last transition doesn't touch transitions[k].resource
        assert(last.resource != transitions[k as int].resource);
    }
}

/// After applying end transitions, every attachment is in its final layout.
pub proof fn lemma_end_transitions_set_final_layouts(
    map: ImageLayoutMap,
    rp: RenderPassState,
    fb_attachments: Seq<ResourceId>,
    k: nat,
)
    requires
        render_pass_well_formed(rp),
        fb_attachments.len() == rp.attachments.len(),
        k < fb_attachments.len(),
        // Attachments are pairwise distinct
        forall|i: int, j: int|
            0 <= i < fb_attachments.len() && 0 <= j < fb_attachments.len() && i != j
            ==> fb_attachments[i] != fb_attachments[j],
    ensures ({
        let result = apply_transitions(map, render_pass_end_transitions(rp, fb_attachments));
        has_layout(result, fb_attachments[k as int], rp.attachments[k as int].final_layout)
    }),
{
    let transitions = render_pass_end_transitions(rp, fb_attachments);

    // Transitions have pairwise-distinct targets (same as fb_attachments)
    assert forall|i: int, j: int|
        0 <= i < transitions.len() && 0 <= j < transitions.len() && i != j
    implies transitions[i].resource != transitions[j].resource by {
        assert(transitions[i].resource == fb_attachments[i]);
        assert(transitions[j].resource == fb_attachments[j]);
    }

    // The k-th transition targets fb_attachments[k] with final_layout
    assert(transitions[k as int].resource == fb_attachments[k as int]);
    assert(transitions[k as int].new_layout == rp.attachments[k as int].final_layout);

    lemma_distinct_transitions_set_kth(map, transitions, k);
}

/// Rendering from Undefined: after a barrier sets up layouts and
/// render pass begins, all attachments are in valid layouts.
pub proof fn lemma_undefined_to_render_pass_valid(
    rp: RenderPassState,
    att_idx: nat,
)
    requires
        render_pass_well_formed(rp),
        att_idx < rp.attachments.len(),
    ensures
        layout_transition_valid(
            ImageLayout::Undefined,
            rp.attachments[att_idx as int].final_layout,
        ),
{
    // final_layout is usable because rp is well-formed
}

/// A well-formed render pass has a valid layout lifecycle.
pub proof fn lemma_well_formed_has_valid_lifecycle(rp: RenderPassState)
    requires render_pass_well_formed(rp),
    ensures render_pass_layout_lifecycle_valid(rp),
{
}

/// Sequential transitions compose: applying [t1, t2] is the same as
/// applying t1 then t2.
pub proof fn lemma_transitions_compose(
    map: ImageLayoutMap,
    t1: LayoutTransition,
    t2: LayoutTransition,
)
    ensures
        apply_transitions(map, seq![t1, t2])
            =~= apply_layout_transition(
                apply_layout_transition(map, t1.resource, t1.new_layout),
                t2.resource,
                t2.new_layout,
            ),
{
    let s2 = seq![t1, t2];
    let s1 = seq![t1];
    let s0 = Seq::<LayoutTransition>::empty();

    // Step 1: s2.drop_last() == s1
    assert(s2.drop_last() =~= s1);
    assert(s2.last() == t2);

    // Step 2: s1.drop_last() == empty
    assert(s1.drop_last() =~= s0);
    assert(s1.last() == t1);

    // Step 3: unfold apply_transitions on empty
    assert(apply_transitions(map, s0) == map);

    // Step 4: unfold apply_transitions on s1
    // apply_transitions(map, s1) = apply_layout_transition(apply_transitions(map, s0), t1.resource, t1.new_layout)
    //                             = apply_layout_transition(map, t1.resource, t1.new_layout)
    let after_t1 = apply_layout_transition(map, t1.resource, t1.new_layout);
    assert(apply_transitions(map, s1) =~= after_t1);

    // Step 5: unfold apply_transitions on s2
    // apply_transitions(map, s2) = apply_layout_transition(apply_transitions(map, s1), t2.resource, t2.new_layout)
    //                             = apply_layout_transition(after_t1, t2.resource, t2.new_layout)
}

/// Applying an empty transition sequence is the identity.
pub proof fn lemma_empty_transitions_identity(map: ImageLayoutMap)
    ensures apply_transitions(map, Seq::empty()) == map,
{
}

/// A layout map where all attachments match initial layouts permits
/// a valid render pass begin.
pub proof fn lemma_matching_initials_permits_begin(
    map: ImageLayoutMap,
    rp: RenderPassState,
    fb_attachments: Seq<ResourceId>,
    att_idx: nat,
)
    requires
        render_pass_well_formed(rp),
        fb_attachments.len() == rp.attachments.len(),
        attachments_match_initial_layouts(map, rp, fb_attachments),
        att_idx < fb_attachments.len(),
        rp.attachments[att_idx as int].initial_layout != ImageLayout::Undefined,
    ensures
        has_layout(map, fb_attachments[att_idx as int], rp.attachments[att_idx as int].initial_layout),
{
    assert(fb_attachments[att_idx as int] == fb_attachments[att_idx as int]); // trigger
}

} // verus!
