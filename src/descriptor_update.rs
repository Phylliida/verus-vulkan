use vstd::prelude::*;
use crate::descriptor::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// A single descriptor write operation.
pub struct DescriptorWrite {
    /// Target descriptor set id.
    pub dst_set: nat,
    /// Target binding index.
    pub dst_binding: nat,
    /// Target array element within the binding.
    pub dst_array_element: nat,
    /// Type of descriptor being written.
    pub descriptor_type: DescriptorType,
    /// Number of descriptors to update.
    pub descriptor_count: nat,
}

/// A single descriptor copy operation.
pub struct DescriptorCopy {
    pub src_set: nat,
    pub src_binding: nat,
    pub src_array_element: nat,
    pub dst_set: nat,
    pub dst_binding: nat,
    pub dst_array_element: nat,
    pub descriptor_count: nat,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// A descriptor write targets a valid binding in the set.
pub open spec fn write_targets_valid_binding(
    write: DescriptorWrite,
    set: DescriptorSetState,
) -> bool {
    set.bindings.contains_key(write.dst_binding)
}

/// A descriptor write type matches the layout binding type.
pub open spec fn write_type_matches_layout(
    write: DescriptorWrite,
    layout: DescriptorSetLayoutState,
) -> bool {
    exists|i: int| 0 <= i < layout.bindings.len()
        && (#[trigger] layout.bindings[i]).binding == write.dst_binding
        && layout.bindings[i].descriptor_type == write.descriptor_type
}

/// Apply a write: mark the binding as non-empty.
pub open spec fn apply_write(
    set: DescriptorSetState,
    write: DescriptorWrite,
    new_binding: DescriptorBinding,
) -> DescriptorSetState {
    DescriptorSetState {
        bindings: set.bindings.insert(write.dst_binding, new_binding),
        ..set
    }
}

/// Apply a copy: copy binding state from source to destination.
pub open spec fn apply_copy(
    dst_set: DescriptorSetState,
    src_set: DescriptorSetState,
    copy: DescriptorCopy,
) -> DescriptorSetState {
    if src_set.bindings.contains_key(copy.src_binding) {
        DescriptorSetState {
            bindings: dst_set.bindings.insert(
                copy.dst_binding,
                src_set.bindings[copy.src_binding],
            ),
            ..dst_set
        }
    } else {
        dst_set
    }
}

/// A batch of writes are all valid.
pub open spec fn all_writes_valid(
    writes: Seq<DescriptorWrite>,
    set: DescriptorSetState,
) -> bool {
    forall|i: int| 0 <= i < writes.len()
        ==> write_targets_valid_binding(#[trigger] writes[i], set)
}

/// Apply a sequence of writes.
pub open spec fn apply_writes(
    set: DescriptorSetState,
    writes: Seq<(DescriptorWrite, DescriptorBinding)>,
) -> DescriptorSetState
    decreases writes.len(),
{
    if writes.len() == 0 {
        set
    } else {
        let (write, binding) = writes.last();
        apply_write(
            apply_writes(set, writes.drop_last()),
            write,
            binding,
        )
    }
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// After a write, the target binding is set.
pub proof fn lemma_write_sets_binding(
    set: DescriptorSetState,
    write: DescriptorWrite,
    new_binding: DescriptorBinding,
)
    ensures
        apply_write(set, write, new_binding)
            .bindings.contains_key(write.dst_binding),
        apply_write(set, write, new_binding)
            .bindings[write.dst_binding] == new_binding,
{
}

/// A write preserves other bindings.
pub proof fn lemma_write_preserves_other_bindings(
    set: DescriptorSetState,
    write: DescriptorWrite,
    new_binding: DescriptorBinding,
    other: nat,
)
    requires
        other != write.dst_binding,
        set.bindings.contains_key(other),
    ensures
        apply_write(set, write, new_binding).bindings[other]
            == set.bindings[other],
{
}

/// A write preserves the set's layout.
pub proof fn lemma_write_preserves_layout(
    set: DescriptorSetState,
    write: DescriptorWrite,
    new_binding: DescriptorBinding,
)
    ensures
        apply_write(set, write, new_binding).layout_id == set.layout_id,
{
}

/// Empty writes don't change the set.
pub proof fn lemma_empty_writes_identity(set: DescriptorSetState)
    ensures
        apply_writes(set, Seq::empty()) == set,
{
}

/// A copy preserves the destination set's layout.
pub proof fn lemma_copy_preserves_layout(
    dst_set: DescriptorSetState,
    src_set: DescriptorSetState,
    copy: DescriptorCopy,
)
    ensures
        apply_copy(dst_set, src_set, copy).layout_id == dst_set.layout_id,
{
}

} // verus!
