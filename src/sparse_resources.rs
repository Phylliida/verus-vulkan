use vstd::prelude::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// A single sparse memory binding: maps a region of a resource to a region of device memory.
pub struct SparseBinding {
    pub resource_offset: nat,
    pub memory_offset: nat,
    pub allocation_id: nat,
    pub size: nat,
}

/// State of a sparse resource.
pub struct SparseResourceState {
    pub id: nat,
    pub alive: bool,
    pub is_sparse: bool,
    pub bindings: Seq<SparseBinding>,
    pub total_blocks: nat,
    pub bound_blocks: nat,
    pub fully_bound: bool,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// Create a fresh sparse resource with no bindings.
pub open spec fn create_sparse_resource(
    id: nat,
    total_blocks: nat,
) -> SparseResourceState {
    SparseResourceState {
        id,
        alive: true,
        is_sparse: true,
        bindings: Seq::empty(),
        total_blocks,
        bound_blocks: 0,
        fully_bound: false,
    }
}

/// A sparse binding is valid: non-zero size and within resource bounds.
pub open spec fn sparse_binding_valid(
    binding: SparseBinding,
    resource: SparseResourceState,
) -> bool {
    binding.size > 0
    && binding.resource_offset + binding.size <= resource.total_blocks
}

/// Ghost update: bind sparse memory (add a binding).
pub open spec fn bind_sparse_memory(
    state: SparseResourceState,
    binding: SparseBinding,
) -> SparseResourceState {
    SparseResourceState {
        bindings: state.bindings.push(binding),
        bound_blocks: state.bound_blocks + binding.size,
        fully_bound: (state.bound_blocks + binding.size) >= state.total_blocks,
        ..state
    }
}

/// Ghost update: unbind sparse memory (remove last binding).
pub open spec fn unbind_sparse_memory(
    state: SparseResourceState,
) -> SparseResourceState
    recommends state.bindings.len() > 0,
{
    if state.bindings.len() == 0 {
        state
    } else {
        let removed = state.bindings.last();
        let new_bound = if state.bound_blocks >= removed.size {
            (state.bound_blocks - removed.size) as nat
        } else {
            0nat
        };
        SparseResourceState {
            bindings: state.bindings.drop_last(),
            bound_blocks: new_bound,
            fully_bound: new_bound >= state.total_blocks,
            ..state
        }
    }
}

/// Two sparse bindings do not overlap in their resource region.
pub open spec fn sparse_bindings_non_overlapping(a: SparseBinding, b: SparseBinding) -> bool {
    a.resource_offset + a.size <= b.resource_offset
    || b.resource_offset + b.size <= a.resource_offset
}

/// All bindings in a sequence are pairwise non-overlapping.
pub open spec fn all_bindings_non_overlapping(bindings: Seq<SparseBinding>) -> bool {
    forall|i: int, j: int|
        0 <= i < bindings.len() && 0 <= j < bindings.len() && i != j
        ==> sparse_bindings_non_overlapping(#[trigger] bindings[i], #[trigger] bindings[j])
}

/// A sparse resource is fully bound when bound_blocks >= total_blocks.
pub open spec fn sparse_fully_bound(state: SparseResourceState) -> bool {
    state.bound_blocks >= state.total_blocks
}

/// A sparse bind operation on a queue is valid.
pub open spec fn queue_sparse_bind_valid(
    state: SparseResourceState,
    binding: SparseBinding,
) -> bool {
    state.alive
    && state.is_sparse
    && sparse_binding_valid(binding, state)
}

/// Destroy a sparse resource.
pub open spec fn destroy_sparse_resource(state: SparseResourceState) -> SparseResourceState {
    SparseResourceState {
        alive: false,
        ..state
    }
}

// ── Lemmas ──────────────────────────────────────────────────────────────

/// A freshly created sparse resource has no bindings.
pub proof fn lemma_fresh_no_bindings(id: nat, total: nat)
    ensures create_sparse_resource(id, total).bindings.len() == 0,
{
}

/// A freshly created sparse resource is alive.
pub proof fn lemma_fresh_is_alive(id: nat, total: nat)
    ensures create_sparse_resource(id, total).alive,
{
}

/// Binding increments bound_blocks by the binding size.
pub proof fn lemma_bind_increments_bound(
    state: SparseResourceState,
    binding: SparseBinding,
)
    ensures
        bind_sparse_memory(state, binding).bound_blocks
            == state.bound_blocks + binding.size,
{
}

/// Binding adds the binding to the sequence.
pub proof fn lemma_bind_appends(
    state: SparseResourceState,
    binding: SparseBinding,
)
    ensures
        bind_sparse_memory(state, binding).bindings
            == state.bindings.push(binding),
{
}

/// A destroyed sparse resource is not alive.
pub proof fn lemma_destroy_not_alive(state: SparseResourceState)
    ensures !destroy_sparse_resource(state).alive,
{
}

/// Destroying preserves the resource id.
pub proof fn lemma_destroy_preserves_id(state: SparseResourceState)
    ensures destroy_sparse_resource(state).id == state.id,
{
}

} // verus!
