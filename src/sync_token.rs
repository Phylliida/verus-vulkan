use vstd::prelude::*;
use crate::resource::*;

verus! {

//  ── Types ───────────────────────────────────────────────────────────────

///  Thread identifier.
pub type ThreadId = nat;

///  Typed identifier for objects tracked by the sync token registry.
///  Prevents collisions between different object kinds (e.g., Buffer{id:5}
///  vs Image{id:5}).
pub enum SyncObjectId {
    ///  A GPU resource (buffer, image, descriptor set, etc.)
    ///  Using ResourceId prevents Buffer{id:5} / Image{id:5} collisions.
    Resource(ResourceId),
    ///  A queue, identified by queue family + queue index.
    Queue(nat),
    ///  A command pool, identified by pool id.
    CommandPool(nat),
    ///  A generic Vulkan handle (fence, semaphore, event, pipeline, etc.)
    ///  Used for objects that don't need typed discrimination.
    Handle(nat),
}

///  Access kind for a tracked object.
pub enum AccessKind {
    ///  Only one thread can hold exclusive access at a time.
    Exclusive,
    ///  Multiple threads can hold shared access simultaneously.
    Shared,
    ///  Object is registered but not currently accessed by any thread.
    Available,
}

///  A ghost synchronization token granting access to a Vulkan object.
///
///  Inspired by Verus linear ghost types and Rust's Send/Sync model.
///  Tokens are linear: acquiring produces one, releasing consumes it.
///  This prevents double-release and ensures access is properly tracked.
pub struct SyncToken {
    ///  The object this token grants access to.
    pub object_id: SyncObjectId,
    ///  The thread holding this token.
    pub holder: ThreadId,
    ///  Whether access is exclusive or shared.
    pub access: AccessKind,
    ///  Generation counter — distinguishes reuse of the same object id.
    pub generation: nat,
}

///  Vulkan operation category, determining sync requirements.
///  Per the Vulkan spec, external synchronization is per-command-parameter,
///  not per-object. This enum captures the relevant categories.
pub enum VulkanOp {
    ///  Mutating operation (destroy, reset, begin/end recording, etc.)
    Mutate,
    ///  Read-only operation (bind pipeline, bind descriptor set during recording, etc.)
    ReadOnly,
    ///  Queue submission (requires exclusive queue access + CBs not held by others).
    QueueSubmit,
    ///  Pool-scoped operation (implicitly synchronizes all children).
    PoolScope,
}

///  The sync requirement for a given operation on a given object.
pub enum SyncRequirement {
    ///  Requires the caller to hold an exclusive token.
    NeedExclusive,
    ///  No token needed — operation is internally thread-safe.
    ThreadSafe,
    ///  Requires either exclusive token on the object, or exclusive token
    ///  on the parent pool (transitive sync).
    NeedExclusiveOrPoolOwner,
}

///  Global token registry: tracks which tokens are currently issued.
///
///  Maps SyncObjectId → current token state.
///  When no token is issued, the object is "available."
pub struct TokenRegistry {
    ///  Per-object state: None = available, Some = token issued.
    pub tokens: Map<SyncObjectId, TokenState>,
    ///  Monotonically increasing generation counter.
    pub next_generation: nat,
}

///  Per-object token state in the registry.
pub struct TokenState {
    ///  Which thread holds the token (if exclusive).
    pub holder: Option<ThreadId>,
    ///  Current access kind (Exclusive, Shared, or Available).
    pub access: AccessKind,
    ///  Number of shared readers (0 when exclusive or available).
    pub shared_count: nat,
    ///  Current generation.
    pub generation: nat,
    ///  Optional parent pool for hierarchical ownership.
    ///  When set, exclusive access to the parent pool grants implicit
    ///  access to this child (transitive synchronization per Vulkan spec).
    pub pool_parent: Option<SyncObjectId>,
}

//  ── Spec Functions ──────────────────────────────────────────────────────

///  Register a new object in the registry (enters Available state).
pub open spec fn register_object(
    reg: TokenRegistry,
    object_id: SyncObjectId,
    pool_parent: Option<SyncObjectId>,
) -> TokenRegistry {
    TokenRegistry {
        tokens: reg.tokens.insert(object_id, TokenState {
            holder: None,
            access: AccessKind::Available,
            shared_count: 0,
            generation: reg.next_generation,
            pool_parent,
        }),
        next_generation: reg.next_generation + 1,
    }
}

///  An object is available: no tokens issued, in Available state.
pub open spec fn object_available(reg: TokenRegistry, object_id: SyncObjectId) -> bool {
    reg.tokens.contains_key(object_id)
    && reg.tokens[object_id].holder.is_none()
    && reg.tokens[object_id].shared_count == 0
    && reg.tokens[object_id].access is Available
}

///  A token is valid: it matches the registry's current state.
pub open spec fn token_valid(reg: TokenRegistry, token: SyncToken) -> bool {
    reg.tokens.contains_key(token.object_id)
    && reg.tokens[token.object_id].generation == token.generation
    && match token.access {
        AccessKind::Exclusive => {
            reg.tokens[token.object_id].holder == Some(token.holder)
            && reg.tokens[token.object_id].access is Exclusive
        },
        AccessKind::Shared => {
            reg.tokens[token.object_id].access is Shared
            && reg.tokens[token.object_id].shared_count > 0
        },
        //  Available is not a valid token access kind — tokens are always
        //  Exclusive or Shared.
        AccessKind::Available => false,
    }
}

///  Acquire an exclusive token: object must be available.
pub open spec fn acquire_exclusive(
    reg: TokenRegistry,
    object_id: SyncObjectId,
    thread: ThreadId,
) -> (TokenRegistry, SyncToken)
    recommends object_available(reg, object_id),
{
    let gen = reg.next_generation;
    let old = reg.tokens[object_id];
    let new_reg = TokenRegistry {
        tokens: reg.tokens.insert(object_id, TokenState {
            holder: Some(thread),
            access: AccessKind::Exclusive,
            shared_count: 0,
            generation: gen,
            pool_parent: old.pool_parent,
        }),
        next_generation: gen + 1,
    };
    let token = SyncToken {
        object_id,
        holder: thread,
        access: AccessKind::Exclusive,
        generation: gen,
    };
    (new_reg, token)
}

///  Release an exclusive token: object becomes available.
pub open spec fn release_exclusive(
    reg: TokenRegistry,
    token: SyncToken,
) -> TokenRegistry
    recommends
        token.access is Exclusive,
        token_valid(reg, token),
{
    let old = reg.tokens[token.object_id];
    TokenRegistry {
        tokens: reg.tokens.insert(token.object_id, TokenState {
            holder: None,
            access: AccessKind::Available,
            shared_count: 0,
            generation: token.generation,
            pool_parent: old.pool_parent,
        }),
        ..reg
    }
}

///  Acquire a shared token: object must be available or already shared.
pub open spec fn acquire_shared(
    reg: TokenRegistry,
    object_id: SyncObjectId,
    thread: ThreadId,
) -> (TokenRegistry, SyncToken)
    recommends
        reg.tokens.contains_key(object_id),
        object_available(reg, object_id)
            || reg.tokens[object_id].access is Shared,
{
    let old = reg.tokens[object_id];
    let gen = old.generation;
    let new_reg = TokenRegistry {
        tokens: reg.tokens.insert(object_id, TokenState {
            holder: None,
            access: AccessKind::Shared,
            shared_count: old.shared_count + 1,
            generation: gen,
            pool_parent: old.pool_parent,
        }),
        ..reg
    };
    let token = SyncToken {
        object_id,
        holder: thread,
        access: AccessKind::Shared,
        generation: gen,
    };
    (new_reg, token)
}

///  Release a shared token: decrements reader count.
///  When the last reader releases, the object returns to Available state.
pub open spec fn release_shared(
    reg: TokenRegistry,
    token: SyncToken,
) -> TokenRegistry
    recommends
        token.access is Shared,
        token_valid(reg, token),
{
    let old = reg.tokens[token.object_id];
    let new_count = (old.shared_count - 1) as nat;
    TokenRegistry {
        tokens: reg.tokens.insert(token.object_id, TokenState {
            holder: None,
            access: if new_count == 0 { AccessKind::Available } else { AccessKind::Shared },
            shared_count: new_count,
            generation: old.generation,
            pool_parent: old.pool_parent,
        }),
        ..reg
    }
}

///  Determine the sync requirement for an operation.
pub open spec fn sync_requirement(op: VulkanOp) -> SyncRequirement {
    match op {
        VulkanOp::Mutate => SyncRequirement::NeedExclusive,
        VulkanOp::ReadOnly => SyncRequirement::ThreadSafe,
        VulkanOp::QueueSubmit => SyncRequirement::NeedExclusive,
        VulkanOp::PoolScope => SyncRequirement::NeedExclusiveOrPoolOwner,
    }
}

///  Whether a thread can perform an operation given the current registry.
pub open spec fn operation_permitted(
    reg: TokenRegistry,
    op: VulkanOp,
    object_id: SyncObjectId,
    thread: ThreadId,
) -> bool {
    match sync_requirement(op) {
        SyncRequirement::NeedExclusive => {
            holds_exclusive(reg, object_id, thread)
        },
        SyncRequirement::ThreadSafe => {
            true
        },
        SyncRequirement::NeedExclusiveOrPoolOwner => {
            //  Direct exclusive access to the object
            holds_exclusive(reg, object_id, thread)
            //  Or implicit access via parent pool ownership
            || (reg.tokens.contains_key(object_id)
                && reg.tokens[object_id].pool_parent.is_some()
                && holds_exclusive(reg, reg.tokens[object_id].pool_parent.unwrap(), thread))
        },
    }
}

///  No data race: an object is either exclusively owned, shared-read, or available.
pub open spec fn no_data_race(reg: TokenRegistry, object_id: SyncObjectId) -> bool {
    reg.tokens.contains_key(object_id)
    && (
        //  Exclusively owned by one thread
        (reg.tokens[object_id].access is Exclusive
         && reg.tokens[object_id].holder.is_some()
         && reg.tokens[object_id].shared_count == 0)
        //  Shared by readers (no exclusive owner)
        || (reg.tokens[object_id].access is Shared
            && reg.tokens[object_id].holder.is_none()
            && reg.tokens[object_id].shared_count > 0)
        //  Available (nobody accessing)
        || object_available(reg, object_id)
    )
}

///  A thread holds exclusive access to an object (convenience predicate).
pub open spec fn holds_exclusive(
    reg: TokenRegistry,
    object_id: SyncObjectId,
    thread: ThreadId,
) -> bool {
    reg.tokens.contains_key(object_id)
    && reg.tokens[object_id].holder == Some(thread)
    && reg.tokens[object_id].access is Exclusive
}

///  No other thread holds exclusive access to an object.
pub open spec fn not_held_by_other(
    reg: TokenRegistry,
    object_id: SyncObjectId,
    except: ThreadId,
) -> bool {
    !reg.tokens.contains_key(object_id)
    || reg.tokens[object_id].holder.is_none()
    || reg.tokens[object_id].holder == Some(except)
    || reg.tokens[object_id].access is Shared
    || reg.tokens[object_id].access is Available
}

//  ── Proofs ──────────────────────────────────────────────────────────────

///  Registering an object makes it available.
pub proof fn lemma_register_makes_available(
    reg: TokenRegistry,
    object_id: SyncObjectId,
    pool_parent: Option<SyncObjectId>,
)
    ensures
        object_available(register_object(reg, object_id, pool_parent), object_id),
{
}

///  Registering preserves other objects.
pub proof fn lemma_register_preserves_others(
    reg: TokenRegistry,
    object_id: SyncObjectId,
    other_id: SyncObjectId,
    pool_parent: Option<SyncObjectId>,
)
    requires
        other_id != object_id,
        reg.tokens.contains_key(other_id),
    ensures
        register_object(reg, object_id, pool_parent).tokens[other_id] == reg.tokens[other_id],
{
}

///  After acquiring exclusive, the token is valid and the thread holds it.
pub proof fn lemma_acquire_exclusive_valid(
    reg: TokenRegistry,
    object_id: SyncObjectId,
    thread: ThreadId,
)
    requires object_available(reg, object_id),
    ensures ({
        let (new_reg, token) = acquire_exclusive(reg, object_id, thread);
        token_valid(new_reg, token)
        && token.holder == thread
        && token.object_id == object_id
        && token.access is Exclusive
        && holds_exclusive(new_reg, object_id, thread)
    }),
{
}

///  After acquiring exclusive, no data race exists.
pub proof fn lemma_acquire_exclusive_no_race(
    reg: TokenRegistry,
    object_id: SyncObjectId,
    thread: ThreadId,
)
    requires object_available(reg, object_id),
    ensures ({
        let (new_reg, _) = acquire_exclusive(reg, object_id, thread);
        no_data_race(new_reg, object_id)
    }),
{
}

///  After releasing exclusive, the object is available.
pub proof fn lemma_release_makes_available(
    reg: TokenRegistry,
    token: SyncToken,
)
    requires
        token.access is Exclusive,
        token_valid(reg, token),
    ensures
        object_available(release_exclusive(reg, token), token.object_id),
{
}

///  Exclusive access blocks other threads.
pub proof fn lemma_exclusive_blocks_others(
    reg: TokenRegistry,
    object_id: SyncObjectId,
    owner: ThreadId,
    other: ThreadId,
)
    requires
        holds_exclusive(reg, object_id, owner),
        owner != other,
    ensures
        !holds_exclusive(reg, object_id, other),
{
}

///  Mutate operations require exclusive access.
pub proof fn lemma_mutate_requires_exclusive(
    reg: TokenRegistry,
    object_id: SyncObjectId,
    thread: ThreadId,
)
    requires
        operation_permitted(reg, VulkanOp::Mutate, object_id, thread),
    ensures
        holds_exclusive(reg, object_id, thread),
{
}

///  Read-only operations are always permitted.
pub proof fn lemma_readonly_always_permitted(
    reg: TokenRegistry,
    object_id: SyncObjectId,
    thread: ThreadId,
)
    ensures
        operation_permitted(reg, VulkanOp::ReadOnly, object_id, thread),
{
}

///  Acquiring/releasing doesn't affect other objects.
pub proof fn lemma_acquire_preserves_others(
    reg: TokenRegistry,
    object_id: SyncObjectId,
    other_id: SyncObjectId,
    thread: ThreadId,
)
    requires
        object_available(reg, object_id),
        other_id != object_id,
        reg.tokens.contains_key(other_id),
    ensures ({
        let (new_reg, _) = acquire_exclusive(reg, object_id, thread);
        new_reg.tokens[other_id] == reg.tokens[other_id]
    }),
{
}

///  Release preserves other objects.
pub proof fn lemma_release_preserves_others(
    reg: TokenRegistry,
    token: SyncToken,
    other_id: SyncObjectId,
)
    requires
        token.access is Exclusive,
        token_valid(reg, token),
        other_id != token.object_id,
        reg.tokens.contains_key(other_id),
    ensures
        release_exclusive(reg, token).tokens[other_id] == reg.tokens[other_id],
{
}

///  Available object has no data race (trivially).
pub proof fn lemma_available_no_race(
    reg: TokenRegistry,
    object_id: SyncObjectId,
)
    requires object_available(reg, object_id),
    ensures no_data_race(reg, object_id),
{
}

///  After acquiring shared, shared count increases.
pub proof fn lemma_acquire_shared_valid(
    reg: TokenRegistry,
    object_id: SyncObjectId,
    thread: ThreadId,
)
    requires
        reg.tokens.contains_key(object_id),
        object_available(reg, object_id)
            || reg.tokens[object_id].access is Shared,
    ensures ({
        let (new_reg, token) = acquire_shared(reg, object_id, thread);
        token_valid(new_reg, token)
        && token.access is Shared
        && new_reg.tokens[object_id].shared_count
            == reg.tokens[object_id].shared_count + 1
    }),
{
}

///  Shared access doesn't grant exclusive.
pub proof fn lemma_shared_not_exclusive(
    reg: TokenRegistry,
    object_id: SyncObjectId,
    thread: ThreadId,
)
    requires
        reg.tokens.contains_key(object_id),
        reg.tokens[object_id].access is Shared,
        reg.tokens[object_id].shared_count > 0,
    ensures
        !holds_exclusive(reg, object_id, thread),
{
}

///  Queue submit requires exclusive queue access.
pub proof fn lemma_submit_requires_exclusive(
    reg: TokenRegistry,
    queue_id: SyncObjectId,
    thread: ThreadId,
)
    requires
        operation_permitted(reg, VulkanOp::QueueSubmit, queue_id, thread),
    ensures
        holds_exclusive(reg, queue_id, thread),
{
}

///  Pool-scoped operations can use parent pool ownership.
pub proof fn lemma_pool_scope_via_parent(
    reg: TokenRegistry,
    object_id: SyncObjectId,
    parent_id: SyncObjectId,
    thread: ThreadId,
)
    requires
        reg.tokens.contains_key(object_id),
        reg.tokens[object_id].pool_parent == Some(parent_id),
        holds_exclusive(reg, parent_id, thread),
    ensures
        operation_permitted(reg, VulkanOp::PoolScope, object_id, thread),
{
}

///  After releasing the last shared reader, object becomes available.
pub proof fn lemma_release_last_shared_makes_available(
    reg: TokenRegistry,
    token: SyncToken,
)
    requires
        token.access is Shared,
        token_valid(reg, token),
        reg.tokens[token.object_id].shared_count == 1,
    ensures
        object_available(release_shared(reg, token), token.object_id),
{
}

///  Acquire exclusive preserves pool_parent.
pub proof fn lemma_acquire_preserves_pool_parent(
    reg: TokenRegistry,
    object_id: SyncObjectId,
    thread: ThreadId,
)
    requires
        object_available(reg, object_id),
    ensures ({
        let (new_reg, _) = acquire_exclusive(reg, object_id, thread);
        new_reg.tokens[object_id].pool_parent == reg.tokens[object_id].pool_parent
    }),
{
}

///  Release exclusive preserves pool_parent.
pub proof fn lemma_release_preserves_pool_parent(
    reg: TokenRegistry,
    token: SyncToken,
)
    requires
        token.access is Exclusive,
        token_valid(reg, token),
    ensures
        release_exclusive(reg, token).tokens[token.object_id].pool_parent
            == reg.tokens[token.object_id].pool_parent,
{
}

} //  verus!
