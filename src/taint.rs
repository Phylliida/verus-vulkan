use vstd::prelude::*;

verus! {

///  Identifies a player / information-flow principal.
pub type PlayerId = nat;

///  Classification of data for information-flow control.
///
///  Used to ensure that one player's private state never leaks
///  into another player's rendered output.
pub enum TaintLabel {
    ///  Visible to all players.
    Public,
    ///  Visible only to the specified player.
    Private { owner: PlayerId },
    ///  Visible only to the server (e.g., hidden game state).
    ServerOnly,
}

///  A set of taint labels, representing the combined classification
///  of a computed value (e.g., output of a compute shader).
pub struct TaintSet {
    pub labels: Set<TaintLabel>,
}

///  True iff every label in `taint` is visible to `viewer`.
///
///  - Public is visible to everyone.
///  - Private{owner} is visible only to that owner.
///  - ServerOnly is never visible to any player.
pub open spec fn visible_to(taint: TaintSet, viewer: PlayerId) -> bool {
    forall|label: TaintLabel| taint.labels.contains(label) ==>
        label_visible_to(label, viewer)
}

///  True iff a single label is visible to the viewer.
pub open spec fn label_visible_to(label: TaintLabel, viewer: PlayerId) -> bool {
    match label {
        TaintLabel::Public => true,
        TaintLabel::Private { owner } => owner == viewer,
        TaintLabel::ServerOnly => false,
    }
}

///  The singleton Public taint set.
pub open spec fn public_taint() -> TaintSet {
    TaintSet { labels: set![TaintLabel::Public] }
}

///  The singleton Private taint set.
pub open spec fn private_taint(owner: PlayerId) -> TaintSet {
    TaintSet { labels: set![TaintLabel::Private { owner }] }
}

///  The singleton ServerOnly taint set.
pub open spec fn server_only_taint() -> TaintSet {
    TaintSet { labels: set![TaintLabel::ServerOnly] }
}

///  The empty taint set (no labels).
pub open spec fn empty_taint() -> TaintSet {
    TaintSet { labels: Set::empty() }
}

///  Union of two taint sets.
pub open spec fn taint_union(a: TaintSet, b: TaintSet) -> TaintSet {
    TaintSet { labels: a.labels.union(b.labels) }
}

//  ── Taint lemmas ──────────────────────────────────────────────────────

///  Public data is visible to every player.
pub proof fn lemma_taint_public_visible_to_all(viewer: PlayerId)
    ensures visible_to(public_taint(), viewer),
{
    assert forall|label: TaintLabel| public_taint().labels.contains(label) implies
        label_visible_to(label, viewer) by {
        //  The only element is Public, which is visible to all.
    }
}

///  Empty taint is vacuously visible to everyone.
pub proof fn lemma_taint_empty_visible_to_all(viewer: PlayerId)
    ensures visible_to(empty_taint(), viewer),
{
    assert forall|label: TaintLabel| empty_taint().labels.contains(label) implies
        label_visible_to(label, viewer) by {
        //  Empty set contains no labels, so the implication is vacuously true.
    }
}

///  A player can see their own private data.
pub proof fn lemma_taint_own_private_visible(owner: PlayerId)
    ensures visible_to(private_taint(owner), owner),
{
    assert forall|label: TaintLabel| private_taint(owner).labels.contains(label) implies
        label_visible_to(label, owner) by {
        //  The only element is Private{owner}, and owner == owner.
    }
}

///  A player cannot see another player's private data.
pub proof fn lemma_taint_other_private_not_visible(owner: PlayerId, viewer: PlayerId)
    requires owner != viewer,
    ensures !visible_to(private_taint(owner), viewer),
{
    //  Witness: Private{owner} is in the set but not visible to viewer.
    assert(private_taint(owner).labels.contains(TaintLabel::Private { owner }));
    assert(!label_visible_to(TaintLabel::Private { owner }, viewer));
}

///  ServerOnly data is not visible to any player.
pub proof fn lemma_taint_server_only_not_visible(viewer: PlayerId)
    ensures !visible_to(server_only_taint(), viewer),
{
    assert(server_only_taint().labels.contains(TaintLabel::ServerOnly));
    assert(!label_visible_to(TaintLabel::ServerOnly, viewer));
}

///  If both sets are visible, their union is visible.
pub proof fn lemma_taint_union_visible(a: TaintSet, b: TaintSet, viewer: PlayerId)
    requires
        visible_to(a, viewer),
        visible_to(b, viewer),
    ensures visible_to(taint_union(a, b), viewer),
{
    assert forall|label: TaintLabel| taint_union(a, b).labels.contains(label) implies
        label_visible_to(label, viewer) by {
        //  label is in a.labels or b.labels; both are visible to viewer.
    }
}

} //  verus!
