use vstd::prelude::*;
use crate::taint::*;
use crate::resource::*;

verus! {

//  ── Spec Functions ──────────────────────────────────────────────────────

///  The taint of a buffer/image after a copy operation.
///  Copy propagates the source's taint to the destination.
pub open spec fn taint_after_copy(
    src_taint: TaintSet,
) -> TaintSet {
    src_taint
}

///  The taint of an output buffer after a compute dispatch.
///  Outputs are tainted with the union of all input taints.
pub open spec fn taint_after_compute(
    input_taints: Seq<TaintSet>,
) -> TaintSet {
    union_all_taints(input_taints)
}

///  Union of all taint sets in a sequence.
pub open spec fn union_all_taints(taints: Seq<TaintSet>) -> TaintSet
    decreases taints.len(),
{
    if taints.len() == 0 {
        empty_taint()
    } else {
        taint_union(
            taints[taints.len() - 1],
            union_all_taints(taints.subrange(0, taints.len() - 1)),
        )
    }
}

///  Taint subset: every label in `a` is also in `b`.
pub open spec fn taint_subset(a: TaintSet, b: TaintSet) -> bool {
    a.labels.subset_of(b.labels)
}

///  A render operation is taint-safe for a viewer if all read resources
///  are visible to that viewer.
pub open spec fn render_taint_safe(
    read_taints: Seq<TaintSet>,
    viewer: PlayerId,
) -> bool {
    forall|i: nat| i < read_taints.len()
        ==> visible_to(read_taints[i as int], viewer)
}

///  The taint of a mixed compute+copy pipeline: copy src, then compute
///  with the result and another input.
pub open spec fn taint_after_copy_then_compute(
    copy_src_taint: TaintSet,
    other_input_taint: TaintSet,
) -> TaintSet {
    taint_after_compute(seq![taint_after_copy(copy_src_taint), other_input_taint])
}

//  ── Proofs ──────────────────────────────────────────────────────────────

///  Copy preserves visibility: if src is visible to viewer, dest is too.
pub proof fn lemma_copy_preserves_visibility(
    src_taint: TaintSet,
    viewer: PlayerId,
)
    requires visible_to(src_taint, viewer),
    ensures visible_to(taint_after_copy(src_taint), viewer),
{
    //  taint_after_copy(src_taint) == src_taint
}

///  If all input taints are visible to a viewer, the compute output is too.
pub proof fn lemma_compute_preserves_visibility(
    input_taints: Seq<TaintSet>,
    viewer: PlayerId,
)
    requires
        forall|i: nat| i < input_taints.len()
            ==> visible_to(input_taints[i as int], viewer),
    ensures
        visible_to(taint_after_compute(input_taints), viewer),
{
    lemma_union_all_preserves_visibility(input_taints, viewer);
}

///  Union of all taint sets preserves visibility (inductive helper).
proof fn lemma_union_all_preserves_visibility(
    taints: Seq<TaintSet>,
    viewer: PlayerId,
)
    requires
        forall|i: nat| i < taints.len()
            ==> visible_to(taints[i as int], viewer),
    ensures
        visible_to(union_all_taints(taints), viewer),
    decreases taints.len(),
{
    if taints.len() == 0 {
        lemma_taint_empty_visible_to_all(viewer);
    } else {
        let last = taints[taints.len() - 1];
        let prefix = taints.subrange(0, taints.len() - 1);

        //  Establish precondition for recursive call
        assert forall|i: nat| i < prefix.len()
            implies visible_to(prefix[i as int], viewer) by {
            assert(prefix[i as int] == taints[i as int]);
        }
        lemma_union_all_preserves_visibility(prefix, viewer);

        //  Union of last and prefix result
        lemma_taint_union_visible(last, union_all_taints(prefix), viewer);
    }
}

///  Taint subset preserves visibility: if a ⊆ b and b is visible, a is visible.
pub proof fn lemma_taint_subset_preserves_visibility(
    sub: TaintSet,
    sup: TaintSet,
    viewer: PlayerId,
)
    requires
        taint_subset(sub, sup),
        visible_to(sup, viewer),
    ensures
        visible_to(sub, viewer),
{
    assert forall|label: TaintLabel| sub.labels.contains(label) implies
        label_visible_to(label, viewer) by {
        assert(sup.labels.contains(label));
    }
}

///  The union of two taint sets is a superset of both.
pub proof fn lemma_taint_union_superset(a: TaintSet, b: TaintSet)
    ensures
        taint_subset(a, taint_union(a, b)),
        taint_subset(b, taint_union(a, b)),
{
}

///  Union is commutative.
pub proof fn lemma_taint_union_commutative(a: TaintSet, b: TaintSet)
    ensures taint_union(a, b).labels =~= taint_union(b, a).labels,
{
}

///  Union is associative.
pub proof fn lemma_taint_union_associative(a: TaintSet, b: TaintSet, c: TaintSet)
    ensures
        taint_union(taint_union(a, b), c).labels
            =~= taint_union(a, taint_union(b, c)).labels,
{
}

///  Union with empty is identity.
pub proof fn lemma_taint_union_empty(a: TaintSet)
    ensures taint_union(a, empty_taint()).labels =~= a.labels,
{
}

///  Adding a private input to a public compute taints the output.
pub proof fn lemma_private_input_taints_output(
    owner: PlayerId,
    viewer: PlayerId,
)
    requires owner != viewer,
    ensures !visible_to(
        taint_after_compute(seq![public_taint(), private_taint(owner)]),
        viewer,
    ),
{
    let result = taint_after_compute(seq![public_taint(), private_taint(owner)]);
    //  result = union_all_taints(seq![public, private(owner)])
    //  = taint_union(private(owner), union_all_taints(seq![public]))
    //  = taint_union(private(owner), taint_union(public, empty))
    //  The result contains Private{owner}, which is not visible to viewer.
    let taints = seq![public_taint(), private_taint(owner)];
    let prefix = taints.subrange(0, 1);
    assert(prefix[0] == public_taint());

    //  union_all_taints(taints) = taint_union(private(owner), union_all_taints(prefix))
    //  union_all_taints(prefix) = taint_union(public, union_all_taints(empty))
    //                           = taint_union(public, empty)
    //  So result.labels contains Private{owner}
    assert(private_taint(owner).labels.contains(TaintLabel::Private { owner }));

    //  taint_union puts private(owner).labels into the result
    let prefix_result = union_all_taints(prefix);
    let full_result = taint_union(private_taint(owner), prefix_result);
    assert(full_result.labels.contains(TaintLabel::Private { owner }));
    assert(!label_visible_to(TaintLabel::Private { owner }, viewer));
}

///  Render safety check: if all resources are public, rendering is safe for anyone.
pub proof fn lemma_all_public_render_safe(
    read_taints: Seq<TaintSet>,
    viewer: PlayerId,
)
    requires
        forall|i: nat| i < read_taints.len()
            ==> read_taints[i as int] == public_taint(),
    ensures
        render_taint_safe(read_taints, viewer),
{
    assert forall|i: nat| i < read_taints.len()
        implies visible_to(read_taints[i as int], viewer) by {
        assert(read_taints[i as int] == public_taint());
        lemma_taint_public_visible_to_all(viewer);
    }
}

///  The render restriction is sound: if render_taint_safe holds,
///  no private data from another player leaks to the viewer.
pub proof fn lemma_render_restriction_sound(
    read_taints: Seq<TaintSet>,
    viewer: PlayerId,
    other_player: PlayerId,
    resource_idx: nat,
)
    requires
        render_taint_safe(read_taints, viewer),
        resource_idx < read_taints.len(),
        viewer != other_player,
    ensures
        //  If the resource contains other_player's private data,
        //  it must also be visible to viewer (contradiction with Private semantics)
        read_taints[resource_idx as int].labels.contains(
            TaintLabel::Private { owner: other_player }
        ) ==> false,
{
    //  render_taint_safe says visible_to(read_taints[resource_idx], viewer)
    //  If it contained Private{other_player}, that label is not visible to viewer
    assert(visible_to(read_taints[resource_idx as int], viewer));
    if read_taints[resource_idx as int].labels.contains(
        TaintLabel::Private { owner: other_player }
    ) {
        assert(label_visible_to(TaintLabel::Private { owner: other_player }, viewer));
        //  But Private{other_player} requires other_player == viewer, contradiction
    }
}

///  Copy then compute: if both sources are visible, result is visible.
pub proof fn lemma_copy_compute_pipeline_visible(
    copy_src_taint: TaintSet,
    other_input_taint: TaintSet,
    viewer: PlayerId,
)
    requires
        visible_to(copy_src_taint, viewer),
        visible_to(other_input_taint, viewer),
    ensures
        visible_to(taint_after_copy_then_compute(copy_src_taint, other_input_taint), viewer),
{
    let copy_result = taint_after_copy(copy_src_taint);
    assert(visible_to(copy_result, viewer));
    let inputs = seq![copy_result, other_input_taint];
    assert forall|i: nat| i < inputs.len()
        implies visible_to(inputs[i as int], viewer) by {
        if i == 0 {
        } else {
        }
    }
    lemma_compute_preserves_visibility(inputs, viewer);
}

} //  verus!
