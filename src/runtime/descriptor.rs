use vstd::prelude::*;
use crate::descriptor::*;
use crate::descriptor_validation::*;
use crate::device::*;
use crate::image_layout::*;
use crate::lifetime::*;
use crate::sync_token::*;
use crate::pool_ownership::*;
use super::device::RuntimeDevice;

verus! {

// ── Runtime Types ───────────────────────────────────────────────────────

/// Runtime wrapper for a descriptor set layout.
pub struct RuntimeDescriptorSetLayout {
    /// Opaque handle (maps to VkDescriptorSetLayout).
    pub handle: u64,
    /// Ghost model of the layout state.
    pub state: Ghost<DescriptorSetLayoutState>,
}

impl View for RuntimeDescriptorSetLayout {
    type V = DescriptorSetLayoutState;
    open spec fn view(&self) -> DescriptorSetLayoutState { self.state@ }
}

/// Runtime wrapper for an allocated descriptor set.
pub struct RuntimeDescriptorSet {
    /// Opaque handle (maps to VkDescriptorSet).
    pub handle: u64,
    /// Ghost model of the set state.
    pub state: Ghost<DescriptorSetState>,
}

impl View for RuntimeDescriptorSet {
    type V = DescriptorSetState;
    open spec fn view(&self) -> DescriptorSetState { self.state@ }
}

/// Runtime wrapper for a descriptor pool.
pub struct RuntimeDescriptorPool {
    /// Opaque handle (maps to VkDescriptorPool).
    pub handle: u64,
    /// Ghost model of the pool state.
    pub state: Ghost<DescriptorPoolState>,
}

impl View for RuntimeDescriptorPool {
    type V = DescriptorPoolState;
    open spec fn view(&self) -> DescriptorPoolState { self.state@ }
}

// ── Well-formedness Specs ───────────────────────────────────────────────

/// Well-formedness of a runtime descriptor set layout.
pub open spec fn runtime_dsl_wf(dsl: &RuntimeDescriptorSetLayout) -> bool {
    dsl@.alive && layout_well_formed(dsl@)
}

/// Well-formedness of a runtime descriptor set.
pub open spec fn runtime_ds_wf(ds: &RuntimeDescriptorSet) -> bool {
    true
}

/// Well-formedness of a runtime descriptor pool.
pub open spec fn runtime_pool_wf(pool: &RuntimeDescriptorPool) -> bool {
    pool@.alive && pool@.max_sets > 0
}

/// Whether a binding at a given slot is non-empty.
pub open spec fn descriptor_bound_at(
    ds: &RuntimeDescriptorSet,
    binding_num: nat,
) -> bool {
    ds@.bindings.contains_key(binding_num)
    && !(ds@.bindings[binding_num] === DescriptorBinding::Empty)
}

/// All bindings in the set match the layout.
pub open spec fn all_descriptors_bound(
    ds: &RuntimeDescriptorSet,
    layout: &RuntimeDescriptorSetLayout,
) -> bool {
    descriptor_set_fully_bound(ds@, layout@)
}

/// Pool has capacity for another set.
pub open spec fn pool_has_capacity(pool: &RuntimeDescriptorPool) -> bool {
    pool_can_allocate(pool@)
}

/// Number of sets allocated from pool.
pub open spec fn pool_allocated_count(pool: &RuntimeDescriptorPool) -> nat {
    pool@.allocated_sets
}

/// Whether set layout matches the given layout ID.
pub open spec fn set_layout_matches(
    ds: &RuntimeDescriptorSet,
    layout_id: nat,
) -> bool {
    ds@.layout_id == layout_id
}

/// Whether a binding is valid for a shader stage.
pub open spec fn binding_valid_for_stage(
    layout: &RuntimeDescriptorSetLayout,
    binding_num: nat,
    _stage: nat,
) -> bool {
    exists|i: int| 0 <= i < layout@.bindings.len()
        && layout@.bindings[i].binding == binding_num
}

// ── Exec Functions ──────────────────────────────────────────────────────

/// Exec: create a descriptor set layout.
pub fn create_descriptor_set_layout_exec(
    handle: u64,
    layout_state: Ghost<DescriptorSetLayoutState>,
) -> (out: RuntimeDescriptorSetLayout)
    requires
        layout_state@.alive,
        layout_well_formed(layout_state@),
    ensures
        out@ == layout_state@,
        runtime_dsl_wf(&out),
{
    RuntimeDescriptorSetLayout {
        handle,
        state: layout_state,
    }
}

/// Exec: create a descriptor pool.
pub fn create_descriptor_pool_exec(
    handle: u64,
    id: Ghost<nat>,
    max_sets: u64,
) -> (out: RuntimeDescriptorPool)
    requires max_sets > 0,
    ensures
        runtime_pool_wf(&out),
        out@.id == id@,
        out@.max_sets == max_sets as nat,
        out@.allocated_sets == 0,
        pool_has_capacity(&out),
{
    RuntimeDescriptorPool {
        handle,
        state: Ghost(DescriptorPoolState {
            id: id@,
            max_sets: max_sets as nat,
            allocated_sets: 0,
            alive: true,
        }),
    }
}

/// Exec: allocate a descriptor set from a pool.
/// Caller must prove pool-level sync (can mutate the pool).
pub fn allocate_descriptor_set_exec(
    pool: &mut RuntimeDescriptorPool,
    handle: u64,
    set_id: Ghost<nat>,
    layout_id: Ghost<nat>,
    thread: Ghost<ThreadId>,
    pool_ownership: Ghost<PoolOwnership>,
    reg: Ghost<TokenRegistry>,
) -> (out: RuntimeDescriptorSet)
    requires
        runtime_pool_wf(&*old(pool)),
        pool_has_capacity(&*old(pool)),
        can_mutate_pool(pool_ownership@, thread@, reg@),
    ensures
        out@.id == set_id@,
        out@.layout_id == layout_id@,
        out@.pool_id == old(pool)@.id,
        out@.bindings == Map::<nat, DescriptorBinding>::empty(),
        pool@ == allocate_from_pool(old(pool)@),
{
    pool.state = Ghost(allocate_from_pool(pool.state@));
    RuntimeDescriptorSet {
        handle,
        state: Ghost(DescriptorSetState {
            id: set_id@,
            layout_id: layout_id@,
            bindings: Map::empty(),
            pool_id: old(pool).state@.id,
        }),
    }
}

/// Exec: update a descriptor binding in a set.
/// Caller must prove the binding exists in the set's layout, the binding is non-Empty,
/// the buffer offset is aligned for the descriptor type, and has access via pool ownership.
pub fn update_descriptor_set_exec(
    ds: &mut RuntimeDescriptorSet,
    layout: Ghost<DescriptorSetLayoutState>,
    binding_num: Ghost<nat>,
    new_binding: Ghost<DescriptorBinding>,
    desc_type: Ghost<DescriptorType>,
    limits: Ghost<DeviceLimits>,
    thread: Ghost<ThreadId>,
    pool_ownership: Ghost<PoolOwnership>,
    reg: Ghost<TokenRegistry>,
    dev: &RuntimeDevice,
)
    requires
        old(ds)@.layout_id == layout@.id,
        layout_contains_binding(layout@, binding_num@),
        !(new_binding@ === DescriptorBinding::Empty),
        descriptor_binding_aligned(new_binding@, desc_type@, limits@),
        can_access_child(pool_ownership@, old(ds)@.id, thread@, reg@),
        descriptor_set_not_in_flight(old(ds)@.id, dev@.pending_submissions),
    ensures
        ds@ == update_descriptor_binding(old(ds)@, binding_num@, new_binding@),
{
    ds.state = Ghost(update_descriptor_binding(ds.state@, binding_num@, new_binding@));
}

/// Exec: free a descriptor set back to its pool.
/// Caller must prove pool-level sync (can mutate the pool).
pub fn free_descriptor_set_exec(
    pool: &mut RuntimeDescriptorPool,
    _ds: &mut RuntimeDescriptorSet,
    dev: &RuntimeDevice,
    thread: Ghost<ThreadId>,
    pool_ownership: Ghost<PoolOwnership>,
    reg: Ghost<TokenRegistry>,
)
    requires
        runtime_pool_wf(&*old(pool)),
        old(pool)@.allocated_sets > 0,
        can_mutate_pool(pool_ownership@, thread@, reg@),
        descriptor_set_not_in_flight(old(_ds)@.id, dev@.pending_submissions),
    ensures
        pool@ == free_to_pool(old(pool)@),
{
    pool.state = Ghost(free_to_pool(pool.state@));
}

/// Exec: destroy a descriptor pool.
/// Vulkan implicitly frees all allocated sets when the pool is destroyed.
/// Caller must prove pool ownership (not just exclusive — must be the pool owner).
pub fn destroy_descriptor_pool_exec(
    pool: &mut RuntimeDescriptorPool,
    dev: &RuntimeDevice,
    thread: Ghost<ThreadId>,
    pool_ownership: Ghost<PoolOwnership>,
    reg: Ghost<TokenRegistry>,
)
    requires
        runtime_pool_wf(&*old(pool)),
        can_mutate_pool(pool_ownership@, thread@, reg@),
        // All pending submissions must be completed before destroying a pool
        forall|i: int| 0 <= i < dev@.pending_submissions.len() ==> (#[trigger] dev@.pending_submissions[i]).completed,
    ensures
        !pool@.alive,
        pool@.id == old(pool)@.id,
{
    pool.state = Ghost(DescriptorPoolState {
        alive: false,
        ..pool.state@
    });
}

/// Exec: destroy a descriptor set layout.
/// Caller must prove exclusive access to the layout.
pub fn destroy_descriptor_set_layout_exec(
    dsl: &mut RuntimeDescriptorSetLayout,
    dev: &RuntimeDevice,
    thread: Ghost<ThreadId>,
    reg: Ghost<TokenRegistry>,
)
    requires
        runtime_dsl_wf(&*old(dsl)),
        holds_exclusive(reg@, SyncObjectId::Handle(old(dsl)@.id), thread@),
        // No pending submission may reference descriptor sets using this layout
        forall|i: int| 0 <= i < dev@.pending_submissions.len() ==> (#[trigger] dev@.pending_submissions[i]).completed,
    ensures
        dsl@ == destroy_descriptor_set_layout_ghost(old(dsl)@),
        !dsl@.alive,
        dsl@.id == old(dsl)@.id,
{
    dsl.state = Ghost(destroy_descriptor_set_layout_ghost(dsl.state@));
}

/// Exec: reset a descriptor pool (frees all allocated sets).
/// Caller must prove pool-level sync (can mutate the pool).
pub fn reset_descriptor_pool_exec(
    pool: &mut RuntimeDescriptorPool,
    dev: &RuntimeDevice,
    thread: Ghost<ThreadId>,
    pool_ownership: Ghost<PoolOwnership>,
    reg: Ghost<TokenRegistry>,
)
    requires
        runtime_pool_wf(&*old(pool)),
        can_mutate_pool(pool_ownership@, thread@, reg@),
        // All pending submissions must be completed before resetting a pool
        forall|i: int| 0 <= i < dev@.pending_submissions.len() ==> (#[trigger] dev@.pending_submissions[i]).completed,
    ensures
        pool@.alive,
        pool@.id == old(pool)@.id,
        pool@.max_sets == old(pool)@.max_sets,
        pool@.allocated_sets == 0,
{
    pool.state = Ghost(DescriptorPoolState {
        allocated_sets: 0,
        ..pool.state@
    });
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// Created pool is well-formed.
pub proof fn lemma_create_pool_wf(id: nat, max_sets: nat)
    requires max_sets > 0,
    ensures ({
        let pool = DescriptorPoolState { id, max_sets, allocated_sets: 0, alive: true };
        pool.alive && pool_can_allocate(pool)
    }),
{
}

/// Allocating a descriptor set preserves pool well-formedness.
pub proof fn lemma_allocate_ds_wf(pool: &RuntimeDescriptorPool)
    requires
        runtime_pool_wf(pool),
        pool_has_capacity(pool),
    ensures
        allocate_from_pool(pool@).alive,
{
    lemma_allocate_increments(pool@);
}

/// Updating a descriptor set preserves its layout_id.
pub proof fn lemma_update_preserves_layout(
    ds: &RuntimeDescriptorSet,
    binding_num: nat,
    new_binding: DescriptorBinding,
)
    ensures
        update_descriptor_binding(ds@, binding_num, new_binding).layout_id == ds@.layout_id,
{
}

/// After writing a non-empty binding, it is bound.
pub proof fn lemma_bound_descriptors_valid(
    ds: &RuntimeDescriptorSet,
    binding_num: nat,
    new_binding: DescriptorBinding,
)
    requires !(new_binding === DescriptorBinding::Empty),
    ensures ({
        let updated = update_descriptor_binding(ds@, binding_num, new_binding);
        updated.bindings.contains_key(binding_num)
        && !(updated.bindings[binding_num] === DescriptorBinding::Empty)
    }),
{
    lemma_update_makes_bound(ds@, binding_num, new_binding);
}

/// Pool capacity decreases after allocation.
pub proof fn lemma_pool_capacity_decreases(pool: &RuntimeDescriptorPool)
    requires
        runtime_pool_wf(pool),
        pool_has_capacity(pool),
    ensures
        allocate_from_pool(pool@).allocated_sets == pool@.allocated_sets + 1,
{
    lemma_allocate_increments(pool@);
}

/// Freeing restores capacity.
pub proof fn lemma_free_restores_capacity(pool: &RuntimeDescriptorPool)
    requires
        runtime_pool_wf(pool),
        pool@.allocated_sets > 0,
    ensures
        free_to_pool(pool@).allocated_sets == pool@.allocated_sets - 1,
{
    lemma_free_decrements(pool@);
}

/// Resetting pool frees all sets and restores full capacity.
pub proof fn lemma_reset_pool_frees_all(pool: &RuntimeDescriptorPool)
    requires runtime_pool_wf(pool),
    ensures ({
        let reset = DescriptorPoolState { allocated_sets: 0, ..pool@ };
        reset.allocated_sets == 0
        && reset.alive
        && reset.max_sets == pool@.max_sets
        && reset.id == pool@.id
        && pool_can_allocate(reset)
    }),
{
}

/// Destroying pool invalidates it and breaks well-formedness.
pub proof fn lemma_destroy_pool_invalidates(pool: &RuntimeDescriptorPool)
    requires runtime_pool_wf(pool),
    ensures ({
        let destroyed = DescriptorPoolState { alive: false, ..pool@ };
        !destroyed.alive
        && destroyed.id == pool@.id
        && destroyed.max_sets == pool@.max_sets
        && destroyed.allocated_sets == pool@.allocated_sets
    }),
{
}

/// In a well-formed layout, binding numbers are unique.
pub proof fn lemma_layout_binding_unique(
    dsl: &RuntimeDescriptorSetLayout,
    i: nat,
    j: nat,
)
    requires
        runtime_dsl_wf(dsl),
        i < dsl@.bindings.len(),
        j < dsl@.bindings.len(),
        i != j,
    ensures
        dsl@.bindings[i as int].binding != dsl@.bindings[j as int].binding,
{
    lemma_bindings_unique_distinct(dsl@, i, j);
}

/// Update is idempotent: writing same binding twice with same value yields same result.
pub proof fn lemma_update_idempotent(
    ds: &RuntimeDescriptorSet,
    binding_num: nat,
    new_binding: DescriptorBinding,
)
    ensures ({
        let once = update_descriptor_binding(ds@, binding_num, new_binding);
        let twice = update_descriptor_binding(once, binding_num, new_binding);
        twice.bindings =~= once.bindings
        && twice.id == once.id
        && twice.layout_id == once.layout_id
        && twice.pool_id == once.pool_id
    }),
{
}

/// Allocate then free roundtrip restores count.
pub proof fn lemma_allocate_free_roundtrip_rt(pool: &RuntimeDescriptorPool)
    requires
        runtime_pool_wf(pool),
        pool_has_capacity(pool),
    ensures
        free_to_pool(allocate_from_pool(pool@)).allocated_sets == pool@.allocated_sets,
{
    lemma_allocate_free_roundtrip(pool@);
}

/// Pipeline compatibility: if all bindings are bound and layout matches, descriptor set is ready.
pub proof fn lemma_pipeline_compatibility(
    ds: &RuntimeDescriptorSet,
    dsl: &RuntimeDescriptorSetLayout,
)
    requires
        runtime_dsl_wf(dsl),
        descriptor_set_fully_bound(ds@, dsl@),
        ds@.layout_id == dsl@.id,
    ensures
        all_descriptors_bound(ds, dsl),
        set_layout_matches(ds, dsl@.id),
{
}

} // verus!
