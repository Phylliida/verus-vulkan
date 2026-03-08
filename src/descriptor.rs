use vstd::prelude::*;
use crate::flags::*;
use crate::image_layout::*;

verus! {

// ── Descriptor Types ──────────────────────────────────────────────────

/// The kind of resource a descriptor binds.
pub enum DescriptorType {
    UniformBuffer,
    StorageBuffer,
    SampledImage,
    StorageImage,
    CombinedImageSampler,
    InputAttachment,
}

/// A single binding slot within a descriptor set layout.
pub struct DescriptorSetLayoutBinding {
    /// Binding number (must be unique within a layout).
    pub binding: nat,
    /// Type of descriptor in this binding.
    pub descriptor_type: DescriptorType,
    /// Number of descriptors in this binding (for arrays; always >= 1).
    pub descriptor_count: nat,
    /// Pipeline stages that can access this binding.
    pub stage_flags: PipelineStageFlags,
}

/// The state of a descriptor set layout object.
pub struct DescriptorSetLayoutState {
    pub id: nat,
    pub bindings: Seq<DescriptorSetLayoutBinding>,
    pub alive: bool,
}

/// What is actually bound at a particular binding slot in a descriptor set.
pub enum DescriptorBinding {
    /// Nothing bound yet.
    Empty,
    /// A buffer region is bound.
    BoundBuffer { buffer_id: nat, offset: nat, range: nat },
    /// An image view is bound.
    BoundImage { image_id: nat, layout: ImageLayout },
}

/// The state of an allocated descriptor set.
pub struct DescriptorSetState {
    /// Unique identifier.
    pub id: nat,
    /// The layout this set was allocated with.
    pub layout_id: nat,
    /// Current bindings: maps binding number → bound resource.
    pub bindings: Map<nat, DescriptorBinding>,
    /// The pool this set was allocated from.
    pub pool_id: nat,
}

/// The state of a descriptor pool.
pub struct DescriptorPoolState {
    pub id: nat,
    /// Maximum number of sets that can be allocated.
    pub max_sets: nat,
    /// Currently allocated set count.
    pub allocated_sets: nat,
    /// Whether this pool is alive (not destroyed).
    pub alive: bool,
}

// ── Spec Functions ────────────────────────────────────────────────────

/// All binding numbers in a layout are distinct.
pub open spec fn bindings_unique(layout: DescriptorSetLayoutState) -> bool {
    forall|i: int, j: int|
        0 <= i < layout.bindings.len()
        && 0 <= j < layout.bindings.len()
        && i != j
        ==> layout.bindings[i].binding != layout.bindings[j].binding
}

/// A descriptor set layout is well-formed:
/// binding numbers are unique and all descriptor counts are positive.
pub open spec fn layout_well_formed(layout: DescriptorSetLayoutState) -> bool {
    bindings_unique(layout)
    && (forall|i: int| 0 <= i < layout.bindings.len() ==>
        layout.bindings[i].descriptor_count > 0)
}

/// The layout contains a binding with the given number, type, and count.
pub open spec fn layout_has_binding(
    layout: DescriptorSetLayoutState,
    binding_num: nat,
    desc_type: DescriptorType,
    count: nat,
) -> bool {
    exists|i: int| 0 <= i < layout.bindings.len()
        && layout.bindings[i].binding == binding_num
        && layout.bindings[i].descriptor_type == desc_type
        && layout.bindings[i].descriptor_count == count
}

/// The layout contains a binding with the given number (regardless of type/count).
pub open spec fn layout_contains_binding(
    layout: DescriptorSetLayoutState,
    binding_num: nat,
) -> bool {
    exists|i: int| 0 <= i < layout.bindings.len()
        && layout.bindings[i].binding == binding_num
}

/// A descriptor binding type matches the layout's expected type for a binding slot.
pub open spec fn binding_type_matches(
    binding: DescriptorBinding,
    desc_type: DescriptorType,
) -> bool {
    match binding {
        DescriptorBinding::Empty => false,
        DescriptorBinding::BoundBuffer { .. } => matches!(desc_type,
            DescriptorType::UniformBuffer | DescriptorType::StorageBuffer),
        DescriptorBinding::BoundImage { .. } => matches!(desc_type,
            DescriptorType::SampledImage | DescriptorType::StorageImage
            | DescriptorType::CombinedImageSampler | DescriptorType::InputAttachment),
    }
}

/// A pool can allocate another set.
pub open spec fn pool_can_allocate(pool: DescriptorPoolState) -> bool {
    pool.alive && pool.allocated_sets < pool.max_sets
}

/// Ghost update: allocate one set from the pool.
pub open spec fn allocate_from_pool(pool: DescriptorPoolState) -> DescriptorPoolState {
    DescriptorPoolState {
        allocated_sets: pool.allocated_sets + 1,
        ..pool
    }
}

/// Ghost update: free one set back to the pool.
pub open spec fn free_to_pool(pool: DescriptorPoolState) -> DescriptorPoolState
    recommends pool.allocated_sets > 0,
{
    DescriptorPoolState {
        allocated_sets: (pool.allocated_sets - 1) as nat,
        ..pool
    }
}

/// A descriptor set is fully bound with respect to its layout:
/// every binding slot declared in the layout has a non-Empty entry.
pub open spec fn descriptor_set_fully_bound(
    dset: DescriptorSetState,
    layout: DescriptorSetLayoutState,
) -> bool {
    forall|i: int| 0 <= i < layout.bindings.len() ==> {
        let b = #[trigger] layout.bindings[i].binding;
        dset.bindings.contains_key(b)
        && !(dset.bindings[b] === DescriptorBinding::Empty)
    }
}

/// Ghost update: write a binding into a descriptor set.
pub open spec fn update_descriptor_binding(
    dset: DescriptorSetState,
    binding_num: nat,
    new_binding: DescriptorBinding,
) -> DescriptorSetState {
    DescriptorSetState {
        bindings: dset.bindings.insert(binding_num, new_binding),
        ..dset
    }
}

// ── Lemmas ────────────────────────────────────────────────────────────

/// A fresh pool (0 allocated, alive) can allocate if max_sets > 0.
pub proof fn lemma_fresh_pool_can_allocate(pool: DescriptorPoolState)
    requires
        pool.alive,
        pool.allocated_sets == 0,
        pool.max_sets > 0,
    ensures
        pool_can_allocate(pool),
{
}

/// allocate_from_pool increments allocated_sets by exactly 1.
pub proof fn lemma_allocate_increments(pool: DescriptorPoolState)
    requires pool_can_allocate(pool),
    ensures
        allocate_from_pool(pool).allocated_sets == pool.allocated_sets + 1,
        allocate_from_pool(pool).id == pool.id,
        allocate_from_pool(pool).max_sets == pool.max_sets,
        allocate_from_pool(pool).alive == pool.alive,
{
}

/// In a well-formed layout, distinct indices have distinct binding numbers.
pub proof fn lemma_bindings_unique_distinct(
    layout: DescriptorSetLayoutState, i: nat, j: nat,
)
    requires
        layout_well_formed(layout),
        i < layout.bindings.len(),
        j < layout.bindings.len(),
        i != j,
    ensures
        layout.bindings[i as int].binding != layout.bindings[j as int].binding,
{
}

/// Updating one binding does not affect other bindings.
pub proof fn lemma_update_preserves_other_bindings(
    dset: DescriptorSetState,
    binding_num: nat,
    new_binding: DescriptorBinding,
    other: nat,
)
    requires
        other != binding_num,
        dset.bindings.contains_key(other),
    ensures
        update_descriptor_binding(dset, binding_num, new_binding)
            .bindings.contains_key(other),
        update_descriptor_binding(dset, binding_num, new_binding)
            .bindings[other] == dset.bindings[other],
{
}

/// After freeing, the pool has one fewer allocated set.
pub proof fn lemma_free_decrements(pool: DescriptorPoolState)
    requires pool.allocated_sets > 0,
    ensures
        free_to_pool(pool).allocated_sets == pool.allocated_sets - 1,
        free_to_pool(pool).id == pool.id,
        free_to_pool(pool).max_sets == pool.max_sets,
{
}

/// After allocating, if still under max, can allocate again.
pub proof fn lemma_allocate_still_under_max(pool: DescriptorPoolState)
    requires
        pool_can_allocate(pool),
        pool.allocated_sets + 1 < pool.max_sets,
    ensures
        pool_can_allocate(allocate_from_pool(pool)),
{
}

/// Allocating then freeing restores the original count.
pub proof fn lemma_allocate_free_roundtrip(pool: DescriptorPoolState)
    requires pool_can_allocate(pool),
    ensures free_to_pool(allocate_from_pool(pool)).allocated_sets == pool.allocated_sets,
{
}

/// Writing a binding slot makes that slot non-empty.
pub proof fn lemma_update_makes_bound(
    dset: DescriptorSetState,
    binding_num: nat,
    new_binding: DescriptorBinding,
)
    requires !(new_binding === DescriptorBinding::Empty),
    ensures ({
        let updated = update_descriptor_binding(dset, binding_num, new_binding);
        updated.bindings.contains_key(binding_num)
        && !(updated.bindings[binding_num] === DescriptorBinding::Empty)
    }),
{
}

} // verus!
