use vstd::prelude::*;
use crate::image_layout::*;
use crate::image_layout_fsm::*;
use crate::resource::*;

verus! {

/// Runtime wrapper for tracking image layout state.
///
/// Wraps the spec-level ImageLayoutMap, allowing exec code to
/// perform layout transitions with verified preconditions.
pub struct RuntimeImageLayoutTracker {
    /// Ghost model: per-resource layout map.
    pub states: Ghost<ImageLayoutMap>,
}

impl View for RuntimeImageLayoutTracker {
    type V = ImageLayoutMap;
    open spec fn view(&self) -> ImageLayoutMap { self.states@ }
}

/// Well-formedness of the layout tracker.
/// No resource is in the Preinitialized layout (Vulkan forbids transitioning to it).
pub open spec fn layout_tracker_wf(tracker: &RuntimeImageLayoutTracker) -> bool {
    forall|r: ResourceId| tracker@.contains_key(r)
        ==> tracker@[r] != ImageLayout::Preinitialized
}

/// Current layout of a specific resource.
pub open spec fn current_layout(
    tracker: &RuntimeImageLayoutTracker,
    resource: ResourceId,
) -> ImageLayout
    recommends tracker@.contains_key(resource),
{
    tracker@[resource]
}

/// Whether a resource is tracked.
pub open spec fn resource_tracked(
    tracker: &RuntimeImageLayoutTracker,
    resource: ResourceId,
) -> bool {
    tracker@.contains_key(resource)
}

/// All tracked resources have usable layouts.
pub open spec fn all_layouts_usable(tracker: &RuntimeImageLayoutTracker) -> bool {
    forall|r: ResourceId| tracker@.contains_key(r) ==>
        is_usable_layout(tracker@[r])
}

/// Whether a transition from current to new layout is valid.
pub open spec fn transition_would_be_valid(
    tracker: &RuntimeImageLayoutTracker,
    resource: ResourceId,
    new_layout: ImageLayout,
) -> bool {
    is_usable_layout(new_layout)
}

/// Whether a layout is a depth layout.
pub open spec fn is_depth_layout(layout: ImageLayout) -> bool {
    matches!(layout,
        ImageLayout::DepthStencilAttachmentOptimal |
        ImageLayout::DepthStencilReadOnlyOptimal
    )
}

/// Whether a layout is a color layout.
pub open spec fn is_color_layout(layout: ImageLayout) -> bool {
    matches!(layout, ImageLayout::ColorAttachmentOptimal)
}

/// Whether a layout is a transfer layout.
pub open spec fn is_transfer_layout(layout: ImageLayout) -> bool {
    matches!(layout,
        ImageLayout::TransferSrcOptimal |
        ImageLayout::TransferDstOptimal
    )
}

/// Number of tracked resources.
pub open spec fn layouts_count(tracker: &RuntimeImageLayoutTracker) -> nat {
    tracker@.dom().len()
}

/// Exec: create a layout tracker with initial resources all Undefined.
pub fn create_layout_tracker_exec(
    resources: Ghost<Set<ResourceId>>,
) -> (out: RuntimeImageLayoutTracker)
    ensures
        layout_tracker_wf(&out),
        out@ == initial_layout_map(resources@),
{
    proof {
        // initial_layout_map sets everything to Undefined, not Preinitialized
        assert forall|r: ResourceId| initial_layout_map(resources@).contains_key(r)
            implies initial_layout_map(resources@)[r] != ImageLayout::Preinitialized by {
            lemma_initial_map_all_undefined(resources@, r);
        };
    }
    RuntimeImageLayoutTracker {
        states: Ghost(initial_layout_map(resources@)),
    }
}

/// Exec: transition a single resource to a new layout.
/// Caller must prove the resource is tracked and its current layout matches old_layout.
/// Pass Undefined as old_layout for "don't care" semantics (contents discarded).
pub fn transition_layout_exec(
    tracker: &mut RuntimeImageLayoutTracker,
    resource: Ghost<ResourceId>,
    old_layout: Ghost<ImageLayout>,
    new_layout: Ghost<ImageLayout>,
)
    requires
        layout_tracker_wf(&*old(tracker)),
        is_usable_layout(new_layout@),
        old(tracker)@.contains_key(resource@),
        old_layout@ == ImageLayout::Undefined || old_layout@ == old(tracker)@[resource@],
    ensures
        layout_tracker_wf(tracker),
        tracker@ == apply_layout_transition(old(tracker)@, resource@, new_layout@),
        tracker@.contains_key(resource@),
        tracker@[resource@] == new_layout@,
{
    tracker.states = Ghost(apply_layout_transition(tracker.states@, resource@, new_layout@));
}

/// Exec: reset a resource layout to Undefined.
pub fn reset_layout_exec(
    tracker: &mut RuntimeImageLayoutTracker,
    resource: Ghost<ResourceId>,
)
    ensures
        tracker@ == apply_layout_transition(old(tracker)@, resource@, ImageLayout::Undefined),
{
    tracker.states = Ghost(apply_layout_transition(tracker.states@, resource@, ImageLayout::Undefined));
}

/// Exec: apply a batch of transitions (ghost-level sequence).
pub fn batch_transition_exec(
    tracker: &mut RuntimeImageLayoutTracker,
    transitions: Ghost<Seq<LayoutTransition>>,
)
    requires
        all_transitions_valid(transitions@),
        // Each transition's resource must be tracked (in the state after prior transitions)
        // and old_layout must match (or be Undefined for "don't care")
        forall|i: int| #![trigger transitions@[i]]
            0 <= i < transitions@.len() ==>
                apply_transitions(old(tracker)@, transitions@.subrange(0, i)).contains_key(transitions@[i].resource)
                && (transitions@[i].old_layout == ImageLayout::Undefined
                    || transitions@[i].old_layout == apply_transitions(old(tracker)@, transitions@.subrange(0, i))[transitions@[i].resource]),
    ensures
        tracker@ == apply_transitions(old(tracker)@, transitions@),
{
    tracker.states = Ghost(apply_transitions(tracker.states@, transitions@));
}

/// Exec: get current layout of a resource (ghost query).
pub fn get_current_layout_exec(
    tracker: &RuntimeImageLayoutTracker,
    resource: Ghost<ResourceId>,
) -> (out: Ghost<ImageLayout>)
    requires
        tracker@.contains_key(resource@),
    ensures
        out@ == tracker@[resource@],
{
    Ghost(tracker.states@[resource@])
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// After transition, the resource has the new layout.
pub proof fn lemma_transition_valid_updates(
    tracker: &RuntimeImageLayoutTracker,
    resource: ResourceId,
    new_layout: ImageLayout,
)
    requires is_usable_layout(new_layout),
    ensures
        has_layout(
            apply_layout_transition(tracker@, resource, new_layout),
            resource,
            new_layout,
        ),
{
    lemma_transition_updates_target(tracker@, resource, new_layout);
}

/// From Undefined, any usable layout is a valid transition target.
pub proof fn lemma_undefined_to_any(
    tracker: &RuntimeImageLayoutTracker,
    resource: ResourceId,
    new_layout: ImageLayout,
)
    requires
        tracker@.contains_key(resource),
        tracker@[resource] == ImageLayout::Undefined,
        is_usable_layout(new_layout),
    ensures
        layout_transition_valid(ImageLayout::Undefined, new_layout),
{
    lemma_undefined_to_any_valid(new_layout);
}

/// After transition, the resource layout is usable.
pub proof fn lemma_usable_after_transition(
    tracker: &RuntimeImageLayoutTracker,
    resource: ResourceId,
    new_layout: ImageLayout,
)
    requires is_usable_layout(new_layout),
    ensures ({
        let new_map = apply_layout_transition(tracker@, resource, new_layout);
        new_map.contains_key(resource) && is_usable_layout(new_map[resource])
    }),
{
}

/// Depth and color layouts are mutually exclusive.
pub proof fn lemma_depth_color_exclusive(layout: ImageLayout)
    ensures !(is_depth_layout(layout) && is_color_layout(layout)),
{
}

/// PresentSrc is a valid transition target.
pub proof fn lemma_present_src_valid(old_layout: ImageLayout)
    ensures layout_transition_valid(old_layout, ImageLayout::PresentSrc),
{
}

/// Transfer layouts are valid transition targets.
pub proof fn lemma_transfer_layouts_valid(old_layout: ImageLayout)
    ensures
        layout_transition_valid(old_layout, ImageLayout::TransferSrcOptimal),
        layout_transition_valid(old_layout, ImageLayout::TransferDstOptimal),
{
}

/// Batch transition is equivalent to sequential application.
pub proof fn lemma_batch_equivalent(
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
    lemma_transitions_compose(map, t1, t2);
}

/// Reset sets layout to Undefined.
pub proof fn lemma_reset_to_undefined(
    tracker: &RuntimeImageLayoutTracker,
    resource: ResourceId,
)
    ensures ({
        let new_map = apply_layout_transition(tracker@, resource, ImageLayout::Undefined);
        new_map.contains_key(resource) && new_map[resource] == ImageLayout::Undefined
    }),
{
}

/// Initial tracker has all resources as Undefined.
pub proof fn lemma_initial_undefined(
    resources: Set<ResourceId>,
    r: ResourceId,
)
    requires resources.contains(r),
    ensures
        initial_layout_map(resources).contains_key(r),
        initial_layout_map(resources)[r] == ImageLayout::Undefined,
{
    lemma_initial_map_all_undefined(resources, r);
}

/// Transition sequence composition: applying [t1..tn, tn+1..tm] equals
/// applying [t1..tn] then [tn+1..tm].
pub proof fn lemma_transition_sequence_composition(
    map: ImageLayoutMap,
    transitions: Seq<LayoutTransition>,
    resource: ResourceId,
    new_layout: ImageLayout,
)
    ensures
        apply_transitions(map, transitions.push(LayoutTransition {
            resource,
            old_layout: ImageLayout::Undefined,
            new_layout,
        })) =~= apply_layout_transition(
            apply_transitions(map, transitions),
            resource,
            new_layout,
        ),
{
    let extended = transitions.push(LayoutTransition {
        resource,
        old_layout: ImageLayout::Undefined,
        new_layout,
    });
    assert(extended.drop_last() =~= transitions);
}

} // verus!
