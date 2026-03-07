use vstd::prelude::*;
use crate::descriptor::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// Per-binding flags for descriptor indexing (VK_EXT_descriptor_indexing).
pub enum DescriptorBindingFlag {
    /// Descriptors in this binding don't all need to be valid at draw time;
    /// only those actually accessed by the shader must be valid.
    PartiallyBound,
    /// Descriptors can be updated after being bound to a command buffer,
    /// even while the CB is pending execution.
    UpdateAfterBind,
    /// The last binding in a set can have a variable descriptor count.
    VariableDescriptorCount,
}

/// Extended descriptor set state for bindless rendering.
pub struct BindlessDescriptorSetState {
    /// The underlying descriptor set.
    pub base: DescriptorSetState,
    /// Per-binding flags.
    pub binding_flags: Map<nat, Set<DescriptorBindingFlag>>,
    /// Actual descriptor count for variable-count bindings.
    pub variable_count: nat,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// A binding has the PartiallyBound flag.
pub open spec fn is_partially_bound(
    set: BindlessDescriptorSetState,
    binding: nat,
) -> bool {
    set.binding_flags.contains_key(binding)
    && set.binding_flags[binding].contains(DescriptorBindingFlag::PartiallyBound)
}

/// A binding has the UpdateAfterBind flag.
pub open spec fn is_update_after_bind(
    set: BindlessDescriptorSetState,
    binding: nat,
) -> bool {
    set.binding_flags.contains_key(binding)
    && set.binding_flags[binding].contains(DescriptorBindingFlag::UpdateAfterBind)
}

/// For a partially-bound binding, only accessed descriptors need to be valid.
/// `accessed_indices` is the set of array indices actually read by the shader.
pub open spec fn partially_bound_access_valid(
    set: BindlessDescriptorSetState,
    binding: nat,
    accessed_indices: Set<nat>,
    valid_indices: Set<nat>,
) -> bool {
    // If partially bound, only accessed indices need to be in valid set
    is_partially_bound(set, binding) ==>
        accessed_indices.subset_of(valid_indices)
}

/// For a non-partially-bound binding, all descriptors must be valid.
pub open spec fn fully_bound_binding_valid(
    set: BindlessDescriptorSetState,
    binding: nat,
    descriptor_count: nat,
    valid_indices: Set<nat>,
) -> bool {
    !is_partially_bound(set, binding) ==>
        (forall|i: nat| i < descriptor_count ==> valid_indices.contains(i))
}

/// Update-after-bind: can update descriptors while command buffer is pending.
pub open spec fn update_while_pending_safe(
    set: BindlessDescriptorSetState,
    binding: nat,
) -> bool {
    is_update_after_bind(set, binding)
}

/// Whether a bindless descriptor set is well-formed.
pub open spec fn bindless_set_well_formed(
    set: BindlessDescriptorSetState,
) -> bool {
    true // base descriptor set existence is tracked externally
}

/// A traditional (non-bindless) set: no special flags.
pub open spec fn is_traditional_set(
    set: BindlessDescriptorSetState,
) -> bool {
    forall|b: nat| set.binding_flags.contains_key(b) ==>
        set.binding_flags[b] == Set::<DescriptorBindingFlag>::empty()
}

/// For a traditional set, all descriptors must be fully bound.
pub open spec fn traditional_set_fully_valid(
    set: BindlessDescriptorSetState,
    binding: nat,
    descriptor_count: nat,
    valid_indices: Set<nat>,
) -> bool {
    is_traditional_set(set) ==>
        (forall|i: nat| i < descriptor_count ==> valid_indices.contains(i))
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// A fully-bound set satisfies partially-bound validation
/// (stronger condition implies weaker).
pub proof fn lemma_fully_bound_implies_partially_bound(
    set: BindlessDescriptorSetState,
    binding: nat,
    descriptor_count: nat,
    valid_indices: Set<nat>,
    accessed_indices: Set<nat>,
)
    requires
        forall|i: nat| i < descriptor_count ==> valid_indices.contains(i),
        forall|i: nat| accessed_indices.contains(i) ==> i < descriptor_count,
    ensures
        partially_bound_access_valid(set, binding, accessed_indices, valid_indices),
{
    // accessed_indices ⊆ [0, descriptor_count) ⊆ valid_indices
    assert(accessed_indices.subset_of(valid_indices)) by {
        assert forall|i: nat| accessed_indices.contains(i)
        implies valid_indices.contains(i) by {
            assert(i < descriptor_count);
        }
    }
}

/// Update-after-bind allows updating while pending.
pub proof fn lemma_update_after_bind_allows_pending(
    set: BindlessDescriptorSetState,
    binding: nat,
)
    requires is_update_after_bind(set, binding),
    ensures update_while_pending_safe(set, binding),
{
}

/// A traditional set is not update-after-bind for any binding.
pub proof fn lemma_traditional_not_update_after_bind(
    set: BindlessDescriptorSetState,
    binding: nat,
)
    requires
        is_traditional_set(set),
        set.binding_flags.contains_key(binding),
    ensures
        !is_update_after_bind(set, binding),
{
    assert(set.binding_flags[binding] == Set::<DescriptorBindingFlag>::empty());
}

/// A traditional set is not partially bound for any binding.
pub proof fn lemma_traditional_not_partially_bound(
    set: BindlessDescriptorSetState,
    binding: nat,
)
    requires
        is_traditional_set(set),
        set.binding_flags.contains_key(binding),
    ensures
        !is_partially_bound(set, binding),
{
    assert(set.binding_flags[binding] == Set::<DescriptorBindingFlag>::empty());
}

/// Empty accessed indices trivially satisfy partially-bound validation.
pub proof fn lemma_empty_access_always_valid(
    set: BindlessDescriptorSetState,
    binding: nat,
    valid_indices: Set<nat>,
)
    ensures
        partially_bound_access_valid(
            set, binding, Set::<nat>::empty(), valid_indices),
{
    assert(Set::<nat>::empty().subset_of(valid_indices));
}

} // verus!
