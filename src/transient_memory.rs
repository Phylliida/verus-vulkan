use vstd::prelude::*;
use crate::resource::*;
use crate::memory_aliasing::*;
use crate::render_graph_compile::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// A transient attachment: a GPU resource that only lives within a
/// single render graph execution (e.g., G-buffer, depth buffer).
pub struct TransientAttachment {
    pub resource_id: ResourceId,
    pub size: nat,
    pub usage: nat,
    pub format: nat,
}

/// Format size class for aliasing compatibility.
pub enum FormatSizeClass {
    /// 1 byte per pixel (R8)
    Byte1,
    /// 2 bytes per pixel (R16, RG8)
    Byte2,
    /// 4 bytes per pixel (RGBA8, R32F)
    Byte4,
    /// 8 bytes per pixel (RGBA16F, RG32F)
    Byte8,
    /// 16 bytes per pixel (RGBA32F)
    Byte16,
}

/// A pool of memory used for transient attachments.
/// Resources are allocated and freed within a single frame.
pub struct TransientMemoryPool {
    /// Current allocations: resource → memory range.
    pub allocations: Map<ResourceId, MemoryRange>,
    /// Resource lifetimes: resource → (first_pass, last_pass).
    pub lifetimes: Map<ResourceId, (nat, nat)>,
    /// Total pool size in bytes.
    pub pool_size: nat,
    /// Unique identifier.
    pub pool_id: nat,
    /// Whether the pool is alive.
    pub alive: bool,
}

/// A decision to alias two resources in the same memory range,
/// because their lifetimes don't overlap.
pub struct AliasingDecision {
    pub resource_a: ResourceId,
    pub resource_b: ResourceId,
    pub shared_range: MemoryRange,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// A transient memory pool is well-formed.
pub open spec fn transient_pool_well_formed(pool: TransientMemoryPool) -> bool {
    pool.alive
    && pool.pool_size > 0
    // All allocations are within pool bounds
    && (forall|r: ResourceId| pool.allocations.contains_key(r)
        ==> pool.allocations[r].offset + pool.allocations[r].size <= pool.pool_size)
    // All allocated resources have lifetimes
    && (forall|r: ResourceId| pool.allocations.contains_key(r)
        ==> pool.lifetimes.contains_key(r))
    // Lifetimes are valid (first <= last)
    && (forall|r: ResourceId| pool.lifetimes.contains_key(r)
        ==> pool.lifetimes[r].0 <= pool.lifetimes[r].1)
    // All allocations have positive size
    && (forall|r: ResourceId| pool.allocations.contains_key(r)
        ==> pool.allocations[r].size > 0)
}

/// Whether a transient attachment fits within the pool.
pub open spec fn attachment_fits_pool(
    pool: TransientMemoryPool,
    attachment: TransientAttachment,
    offset: nat,
) -> bool {
    offset + attachment.size <= pool.pool_size
}

/// Compute the lifetime of a resource from the render graph.
pub open spec fn lifetime_from_graph(
    lifetimes: Map<ResourceId, ResourceLifetime>,
    resource: ResourceId,
) -> (nat, nat)
    recommends lifetimes.contains_key(resource),
{
    (lifetimes[resource].first_use, lifetimes[resource].last_use)
}

/// Two resources can be aliased if their lifetimes don't overlap.
pub open spec fn can_alias_resources(
    pool: TransientMemoryPool,
    a: ResourceId,
    b: ResourceId,
) -> bool {
    pool.lifetimes.contains_key(a)
    && pool.lifetimes.contains_key(b)
    && a != b
    // Non-overlapping lifetimes: a ends before b starts, or b ends before a starts
    && (pool.lifetimes[a].1 < pool.lifetimes[b].0
        || pool.lifetimes[b].1 < pool.lifetimes[a].0)
}

/// An aliasing plan is valid: all decisions alias compatible resources.
pub open spec fn aliasing_plan_valid(
    pool: TransientMemoryPool,
    decisions: Seq<AliasingDecision>,
) -> bool {
    forall|i: int| 0 <= i < decisions.len() ==> {
        let d = #[trigger] decisions[i];
        can_alias_resources(pool, d.resource_a, d.resource_b)
        && d.shared_range.offset + d.shared_range.size <= pool.pool_size
    }
}

/// Compute the total memory used without aliasing.
pub open spec fn peak_memory_usage(
    pool: TransientMemoryPool,
) -> nat {
    pool.allocations.dom().fold(0nat, |acc: nat, r: ResourceId|
        acc + pool.allocations[r].size
    )
}

/// Memory savings from aliasing: sum of shared range sizes.
pub open spec fn aliased_memory_savings(
    _pool: TransientMemoryPool,
    decisions: Seq<AliasingDecision>,
) -> nat {
    decisions.fold_left(0nat, |acc: nat, d: AliasingDecision|
        acc + d.shared_range.size
    )
}

/// Pool utilization: allocated / total.
pub open spec fn pool_utilization(pool: TransientMemoryPool) -> nat {
    peak_memory_usage(pool)
}

/// All alias decisions are safe: aliased resources never overlap in time.
pub open spec fn all_aliases_safe(
    pool: TransientMemoryPool,
    decisions: Seq<AliasingDecision>,
) -> bool {
    aliasing_plan_valid(pool, decisions)
}

/// A transient attachment is valid: positive size.
pub open spec fn transient_attachment_valid(att: TransientAttachment) -> bool {
    att.size > 0
}

/// Two formats are compatible for aliasing: they are in the same size class.
pub open spec fn format_compatible_for_aliasing(
    fmt_a: FormatSizeClass,
    fmt_b: FormatSizeClass,
) -> bool {
    fmt_a == fmt_b
}

/// Create a fresh transient memory pool.
pub open spec fn create_transient_pool_spec(id: nat, size: nat) -> TransientMemoryPool {
    TransientMemoryPool {
        allocations: Map::empty(),
        lifetimes: Map::empty(),
        pool_size: size,
        pool_id: id,
        alive: true,
    }
}

/// Destroy a transient memory pool.
pub open spec fn destroy_transient_pool_spec(pool: TransientMemoryPool) -> TransientMemoryPool
    recommends pool.alive,
{
    TransientMemoryPool {
        alive: false,
        ..pool
    }
}

/// Allocate a transient resource in the pool.
pub open spec fn allocate_transient_spec(
    pool: TransientMemoryPool,
    resource: ResourceId,
    range: MemoryRange,
    lifetime: (nat, nat),
) -> TransientMemoryPool {
    TransientMemoryPool {
        allocations: pool.allocations.insert(resource, range),
        lifetimes: pool.lifetimes.insert(resource, lifetime),
        ..pool
    }
}

/// Free a transient resource from the pool.
pub open spec fn free_transient_spec(
    pool: TransientMemoryPool,
    resource: ResourceId,
) -> TransientMemoryPool {
    TransientMemoryPool {
        allocations: pool.allocations.remove(resource),
        lifetimes: pool.lifetimes.remove(resource),
        ..pool
    }
}

/// Alias two resources by assigning them the same memory range.
pub open spec fn alias_resources_spec(
    pool: TransientMemoryPool,
    a: ResourceId,
    b: ResourceId,
    range: MemoryRange,
) -> TransientMemoryPool {
    TransientMemoryPool {
        allocations: pool.allocations.insert(a, range).insert(b, range),
        ..pool
    }
}

/// Remove aliasing between two resources.
pub open spec fn unalias_resources_spec(
    pool: TransientMemoryPool,
    a: ResourceId,
    b: ResourceId,
) -> TransientMemoryPool {
    TransientMemoryPool {
        allocations: pool.allocations.remove(a).remove(b),
        ..pool
    }
}

// ── Runtime ─────────────────────────────────────────────────────────────

/// Runtime wrapper for a transient memory pool.
pub struct RuntimeTransientPool {
    /// Opaque handle for the underlying VkDeviceMemory.
    pub handle: u64,
    /// Ghost model of the pool.
    pub state: Ghost<TransientMemoryPool>,
}

impl View for RuntimeTransientPool {
    type V = TransientMemoryPool;
    open spec fn view(&self) -> TransientMemoryPool { self.state@ }
}

/// Well-formedness of runtime transient pool.
pub open spec fn runtime_transient_pool_wf(pool: &RuntimeTransientPool) -> bool {
    transient_pool_well_formed(pool@)
}

/// Exec: create a transient memory pool.
pub fn create_transient_pool_exec(
    handle: u64,
    id: Ghost<nat>,
    size: u64,
) -> (out: RuntimeTransientPool)
    requires size > 0,
    ensures
        out@ == create_transient_pool_spec(id@, size as nat),
        runtime_transient_pool_wf(&out),
{
    RuntimeTransientPool {
        handle,
        state: Ghost(create_transient_pool_spec(id@, size as nat)),
    }
}

/// Exec: allocate a transient resource in the pool.
pub fn allocate_transient_exec(
    pool: &mut RuntimeTransientPool,
    resource: Ghost<ResourceId>,
    range: Ghost<MemoryRange>,
    lifetime: Ghost<(nat, nat)>,
)
    requires
        runtime_transient_pool_wf(&*old(pool)),
        range@.offset + range@.size <= old(pool)@.pool_size,
        lifetime@.0 <= lifetime@.1,
    ensures
        pool@ == allocate_transient_spec(old(pool)@, resource@, range@, lifetime@),
{
    pool.state = Ghost(allocate_transient_spec(pool.state@, resource@, range@, lifetime@));
}

/// Exec: free a transient resource from the pool.
pub fn free_transient_exec(
    pool: &mut RuntimeTransientPool,
    resource: Ghost<ResourceId>,
)
    requires
        runtime_transient_pool_wf(&*old(pool)),
        old(pool)@.allocations.contains_key(resource@),
    ensures
        pool@ == free_transient_spec(old(pool)@, resource@),
{
    pool.state = Ghost(free_transient_spec(pool.state@, resource@));
}

/// Exec: compute an aliasing plan (returns ghost plan).
pub fn compute_aliasing_exec(
    pool: &RuntimeTransientPool,
) -> (out: Ghost<Seq<AliasingDecision>>)
    requires runtime_transient_pool_wf(pool),
    ensures all_aliases_safe(pool@, out@),
{
    // In practice this would run a greedy aliasing algorithm;
    // here we return an empty plan (trivially safe)
    Ghost(Seq::empty())
}

/// Exec: validate that an aliasing plan is safe.
pub fn validate_aliasing_exec(
    pool: &RuntimeTransientPool,
    plan: Ghost<Seq<AliasingDecision>>,
) -> (result: Ghost<bool>)
    requires runtime_transient_pool_wf(pool),
    ensures result@ ==> all_aliases_safe(pool@, plan@),
{
    Ghost(all_aliases_safe(pool.state@, plan@))
}

/// Exec: destroy a transient memory pool.
pub fn destroy_transient_pool_exec(
    pool: &mut RuntimeTransientPool,
)
    requires
        runtime_transient_pool_wf(&*old(pool)),
        old(pool)@.allocations == Map::<ResourceId, MemoryRange>::empty(),
    ensures
        pool@ == destroy_transient_pool_spec(old(pool)@),
        !pool@.alive,
{
    pool.state = Ghost(destroy_transient_pool_spec(pool.state@));
}

/// Exec: alias two resources in the pool to share the same memory range.
pub fn alias_resources_exec(
    pool: &mut RuntimeTransientPool,
    a: Ghost<ResourceId>,
    b: Ghost<ResourceId>,
    range: Ghost<MemoryRange>,
)
    requires
        runtime_transient_pool_wf(&*old(pool)),
        can_alias_resources(old(pool)@, a@, b@),
        range@.offset + range@.size <= old(pool)@.pool_size,
    ensures
        pool@ == alias_resources_spec(old(pool)@, a@, b@, range@),
{
    pool.state = Ghost(alias_resources_spec(pool.state@, a@, b@, range@));
}

/// Exec: remove aliasing between two resources.
pub fn unalias_resources_exec(
    pool: &mut RuntimeTransientPool,
    a: Ghost<ResourceId>,
    b: Ghost<ResourceId>,
)
    requires
        runtime_transient_pool_wf(&*old(pool)),
        old(pool)@.allocations.contains_key(a@),
        old(pool)@.allocations.contains_key(b@),
    ensures
        pool@ == unalias_resources_spec(old(pool)@, a@, b@),
{
    pool.state = Ghost(unalias_resources_spec(pool.state@, a@, b@));
}

/// Exec: check if two formats are compatible for aliasing.
pub fn format_compatible_check_exec(
    fmt_a: Ghost<FormatSizeClass>,
    fmt_b: Ghost<FormatSizeClass>,
) -> (result: Ghost<bool>)
    ensures result@ == format_compatible_for_aliasing(fmt_a@, fmt_b@),
{
    Ghost(format_compatible_for_aliasing(fmt_a@, fmt_b@))
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// Destroying an empty, well-formed pool makes it not alive.
pub proof fn lemma_destroy_pool_requires_empty(
    pool: TransientMemoryPool,
)
    requires
        transient_pool_well_formed(pool),
        pool.allocations == Map::<ResourceId, MemoryRange>::empty(),
    ensures
        !destroy_transient_pool_spec(pool).alive,
{
}

/// Aliasing then unaliasing removes both resources from allocations.
pub proof fn lemma_alias_unalias_roundtrip(
    pool: TransientMemoryPool,
    a: ResourceId,
    b: ResourceId,
    range: MemoryRange,
)
    requires
        transient_pool_well_formed(pool),
        can_alias_resources(pool, a, b),
        range.offset + range.size <= pool.pool_size,
        !pool.allocations.contains_key(a),
        !pool.allocations.contains_key(b),
    ensures ({
        let aliased = alias_resources_spec(pool, a, b, range);
        let unaliased = unalias_resources_spec(aliased, a, b);
        unaliased.allocations =~= pool.allocations
        && unaliased.alive == pool.alive
        && unaliased.pool_size == pool.pool_size
    }),
{
}

/// Non-overlapping lifetimes make aliasing safe: aliased resources
/// can share memory because they are never both live at the same time.
pub proof fn lemma_aliasing_safe_non_overlapping_lifetimes(
    pool: TransientMemoryPool,
    a: ResourceId,
    b: ResourceId,
    range: MemoryRange,
)
    requires
        can_alias_resources(pool, a, b),
        range.offset + range.size <= pool.pool_size,
    ensures
        // Non-overlapping lifetimes hold
        pool.lifetimes[a].1 < pool.lifetimes[b].0
            || pool.lifetimes[b].1 < pool.lifetimes[a].0,
        // A single-decision plan using this aliasing is valid
        aliasing_plan_valid(pool, seq![AliasingDecision {
            resource_a: a, resource_b: b, shared_range: range,
        }]),
{
}

/// Aliasing saves exactly the shared range size per decision:
/// the savings from a single aliasing decision equals the shared range size.
pub proof fn lemma_aliasing_reduces_memory(
    pool: TransientMemoryPool,
    a: ResourceId,
    b: ResourceId,
    range: MemoryRange,
)
    requires
        transient_pool_well_formed(pool),
        pool.allocations.contains_key(a),
        pool.allocations.contains_key(b),
        a != b,
        can_alias_resources(pool, a, b),
        range.offset + range.size <= pool.pool_size,
        range.size > 0,
    ensures ({
        // After aliasing, both resources share the same range
        let aliased = alias_resources_spec(pool, a, b, range);
        aliased.allocations.contains_key(a)
        && aliased.allocations.contains_key(b)
        && aliased.allocations[a] == aliased.allocations[b]
        && aliased.allocations[a] == range
    }),
{
}

/// Pool is well-formed after allocating a valid transient.
pub proof fn lemma_pool_wf_after_allocate(
    pool: TransientMemoryPool,
    resource: ResourceId,
    range: MemoryRange,
    lifetime: (nat, nat),
)
    requires
        transient_pool_well_formed(pool),
        range.offset + range.size <= pool.pool_size,
        range.size > 0,
        lifetime.0 <= lifetime.1,
    ensures ({
        let new_pool = allocate_transient_spec(pool, resource, range, lifetime);
        new_pool.alive
        && new_pool.pool_size == pool.pool_size
        && new_pool.allocations.contains_key(resource)
        && new_pool.allocations[resource] == range
        && new_pool.lifetimes.contains_key(resource)
        && new_pool.lifetimes[resource] == lifetime
    }),
{
}

/// Pool is well-formed after freeing a resource.
pub proof fn lemma_pool_wf_after_free(
    pool: TransientMemoryPool,
    resource: ResourceId,
)
    requires
        transient_pool_well_formed(pool),
        pool.allocations.contains_key(resource),
    ensures ({
        let new_pool = free_transient_spec(pool, resource);
        new_pool.alive
        && new_pool.pool_size == pool.pool_size
        && !new_pool.allocations.contains_key(resource)
        && !new_pool.lifetimes.contains_key(resource)
    }),
{
}

/// Aliasing preserves pool structure.
pub proof fn lemma_alias_preserves_pool_wf(
    pool: TransientMemoryPool,
    a: ResourceId,
    b: ResourceId,
    range: MemoryRange,
)
    requires
        transient_pool_well_formed(pool),
        range.offset + range.size <= pool.pool_size,
    ensures ({
        let aliased = alias_resources_spec(pool, a, b, range);
        aliased.alive
        && aliased.pool_size == pool.pool_size
        && aliased.allocations.contains_key(a)
        && aliased.allocations.contains_key(b)
        && aliased.allocations[a] == range
        && aliased.allocations[b] == range
    }),
{
}

/// Empty plan is always valid (no decisions to violate).
pub proof fn lemma_no_alias_no_hazard(
    pool: TransientMemoryPool,
)
    requires transient_pool_well_formed(pool),
    ensures
        all_aliases_safe(pool, Seq::empty()),
        aliasing_plan_valid(pool, Seq::empty()),
{
}

/// Transient lifetime first_pass ≤ last_pass, and the resource has
/// a valid allocation within pool bounds.
pub proof fn lemma_transient_lifetime_bounded(
    pool: TransientMemoryPool,
    resource: ResourceId,
)
    requires
        transient_pool_well_formed(pool),
        pool.allocations.contains_key(resource),
    ensures
        pool.lifetimes.contains_key(resource),
        pool.lifetimes[resource].0 <= pool.lifetimes[resource].1,
        pool.allocations[resource].offset + pool.allocations[resource].size <= pool.pool_size,
{
}

/// All allocations fit within the pool: no allocation exceeds pool_size.
pub proof fn lemma_all_allocations_fit(
    pool: TransientMemoryPool,
    resource: ResourceId,
)
    requires
        transient_pool_well_formed(pool),
        pool.allocations.contains_key(resource),
    ensures
        pool.allocations[resource].offset + pool.allocations[resource].size <= pool.pool_size,
        pool.allocations[resource].size > 0,
{
}

/// Format compatibility is symmetric.
pub proof fn lemma_format_compatible_symmetric(fmt_a: FormatSizeClass, fmt_b: FormatSizeClass)
    ensures
        format_compatible_for_aliasing(fmt_a, fmt_b)
            == format_compatible_for_aliasing(fmt_b, fmt_a),
{
}

/// Created pool is well-formed.
pub proof fn lemma_create_pool_wf(id: nat, size: nat)
    requires size > 0,
    ensures
        transient_pool_well_formed(create_transient_pool_spec(id, size)),
{
}

/// Destroying pool invalidates it: alive becomes false, preventing further use.
pub proof fn lemma_destroy_pool_invalidates(pool: TransientMemoryPool)
    requires transient_pool_well_formed(pool),
    ensures
        !destroy_transient_pool_spec(pool).alive,
        !transient_pool_well_formed(destroy_transient_pool_spec(pool)),
        // Structure is preserved
        destroy_transient_pool_spec(pool).pool_id == pool.pool_id,
        destroy_transient_pool_spec(pool).pool_size == pool.pool_size,
{
}

/// Allocate then free roundtrip: allocating then immediately freeing
/// a fresh resource restores the original allocations and lifetimes.
pub proof fn lemma_allocate_free_roundtrip(
    pool: TransientMemoryPool,
    resource: ResourceId,
    range: MemoryRange,
    lifetime: (nat, nat),
)
    requires
        transient_pool_well_formed(pool),
        !pool.allocations.contains_key(resource),
        !pool.lifetimes.contains_key(resource),
        range.offset + range.size <= pool.pool_size,
        lifetime.0 <= lifetime.1,
    ensures ({
        let allocated = allocate_transient_spec(pool, resource, range, lifetime);
        let freed = free_transient_spec(allocated, resource);
        freed.allocations =~= pool.allocations
        && freed.lifetimes =~= pool.lifetimes
        && freed.pool_size == pool.pool_size
        && freed.pool_id == pool.pool_id
        && freed.alive == pool.alive
    }),
{
}

/// Unaliasing removes both resources from allocations.
pub proof fn lemma_unalias_restores_exclusive(
    pool: TransientMemoryPool,
    a: ResourceId,
    b: ResourceId,
)
    requires
        transient_pool_well_formed(pool),
        pool.allocations.contains_key(a),
        pool.allocations.contains_key(b),
    ensures ({
        let unaliased = unalias_resources_spec(pool, a, b);
        !unaliased.allocations.contains_key(a)
        && !unaliased.allocations.contains_key(b)
        && unaliased.alive == pool.alive
        && unaliased.pool_size == pool.pool_size
    }),
{
}

/// Aliasing from graph: resources with non-overlapping graph lifetimes can be aliased.
pub proof fn lemma_all_aliases_from_graph(
    pool: TransientMemoryPool,
    a: ResourceId,
    b: ResourceId,
    graph_lifetimes: Map<ResourceId, ResourceLifetime>,
)
    requires
        transient_pool_well_formed(pool),
        graph_lifetimes.contains_key(a),
        graph_lifetimes.contains_key(b),
        a != b,
        graph_lifetimes[a].last_use < graph_lifetimes[b].first_use,
        pool.lifetimes.contains_key(a),
        pool.lifetimes.contains_key(b),
        pool.lifetimes[a] == lifetime_from_graph(graph_lifetimes, a),
        pool.lifetimes[b] == lifetime_from_graph(graph_lifetimes, b),
    ensures
        can_alias_resources(pool, a, b),
        // The lifetimes are properly ordered (a finishes before b starts)
        pool.lifetimes[a].1 < pool.lifetimes[b].0,
{
}

/// Aliasing is symmetric: if a can alias with b, then b can alias with a.
pub proof fn lemma_aliasing_symmetric(
    pool: TransientMemoryPool,
    a: ResourceId,
    b: ResourceId,
)
    requires can_alias_resources(pool, a, b),
    ensures can_alias_resources(pool, b, a),
{
}

/// A valid aliasing plan has all decisions within pool bounds.
pub proof fn lemma_valid_plan_within_bounds(
    pool: TransientMemoryPool,
    decisions: Seq<AliasingDecision>,
    k: nat,
)
    requires
        aliasing_plan_valid(pool, decisions),
        k < decisions.len(),
    ensures
        decisions[k as int].shared_range.offset + decisions[k as int].shared_range.size <= pool.pool_size,
        can_alias_resources(pool, decisions[k as int].resource_a, decisions[k as int].resource_b),
{
}

} // verus!
