use vstd::prelude::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// Thread identifier.
pub type ThreadId = nat;

/// Access kind: exclusive (write) or shared (read).
pub enum AccessKind {
    /// Only one thread can hold exclusive access at a time.
    Exclusive,
    /// Multiple threads can hold shared access simultaneously.
    Shared,
}

/// A ghost synchronization token granting access to a Vulkan object.
///
/// Inspired by Verus linear ghost types and Rust's Send/Sync model.
/// Tokens are linear: acquiring produces one, releasing consumes it.
/// This prevents double-release and ensures access is properly tracked.
pub struct SyncToken {
    /// The object this token grants access to.
    pub object_id: nat,
    /// The thread holding this token.
    pub holder: ThreadId,
    /// Whether access is exclusive or shared.
    pub access: AccessKind,
    /// Generation counter — distinguishes reuse of the same object id.
    pub generation: nat,
}

/// Vulkan operation category, determining sync requirements.
/// Per the Vulkan spec, external synchronization is per-command-parameter,
/// not per-object. This enum captures the relevant categories.
pub enum VulkanOp {
    /// Mutating operation (destroy, reset, begin/end recording, etc.)
    Mutate,
    /// Read-only operation (bind pipeline, bind descriptor set during recording, etc.)
    ReadOnly,
    /// Queue submission (requires exclusive queue access + CBs not held by others).
    QueueSubmit,
    /// Pool-scoped operation (implicitly synchronizes all children).
    PoolScope,
}

/// The sync requirement for a given operation on a given object.
pub enum SyncRequirement {
    /// Requires the caller to hold an exclusive token.
    NeedExclusive,
    /// No token needed — operation is internally thread-safe.
    ThreadSafe,
    /// Requires either exclusive token on the object, or exclusive token
    /// on the parent pool (transitive sync).
    NeedExclusiveOrPoolOwner,
}

/// Global token registry: tracks which tokens are currently issued.
///
/// Maps object_id → current token state.
/// When no token is issued, the object is "available."
pub struct TokenRegistry {
    /// Per-object state: None = available, Some = token issued.
    pub tokens: Map<nat, TokenState>,
    /// Monotonically increasing generation counter.
    pub next_generation: nat,
}

/// Per-object token state in the registry.
pub struct TokenState {
    /// Which thread holds the token (if exclusive).
    pub holder: Option<ThreadId>,
    /// Current access kind.
    pub access: AccessKind,
    /// Number of shared readers (0 when exclusive or available).
    pub shared_count: nat,
    /// Current generation.
    pub generation: nat,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// An object is available: no tokens issued.
pub open spec fn object_available(reg: TokenRegistry, object_id: nat) -> bool {
    reg.tokens.contains_key(object_id)
    && reg.tokens[object_id].holder.is_none()
    && reg.tokens[object_id].shared_count == 0
}

/// A token is valid: it matches the registry's current state.
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
    }
}

/// Acquire an exclusive token: object must be available.
pub open spec fn acquire_exclusive(
    reg: TokenRegistry,
    object_id: nat,
    thread: ThreadId,
) -> (TokenRegistry, SyncToken)
    recommends object_available(reg, object_id),
{
    let gen = reg.next_generation;
    let new_reg = TokenRegistry {
        tokens: reg.tokens.insert(object_id, TokenState {
            holder: Some(thread),
            access: AccessKind::Exclusive,
            shared_count: 0,
            generation: gen,
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

/// Release an exclusive token: object becomes available.
pub open spec fn release_exclusive(
    reg: TokenRegistry,
    token: SyncToken,
) -> TokenRegistry
    recommends
        token.access is Exclusive,
        token_valid(reg, token),
{
    TokenRegistry {
        tokens: reg.tokens.insert(token.object_id, TokenState {
            holder: None,
            access: AccessKind::Shared, // reset to neutral
            shared_count: 0,
            generation: token.generation,
        }),
        ..reg
    }
}

/// Acquire a shared token: object must be available or already shared.
pub open spec fn acquire_shared(
    reg: TokenRegistry,
    object_id: nat,
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

/// Release a shared token: decrements reader count.
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
            holder: if new_count == 0 { None } else { old.holder },
            access: if new_count == 0 { AccessKind::Shared } else { AccessKind::Shared },
            shared_count: new_count,
            generation: old.generation,
        }),
        ..reg
    }
}

/// Determine the sync requirement for an operation.
pub open spec fn sync_requirement(op: VulkanOp) -> SyncRequirement {
    match op {
        VulkanOp::Mutate => SyncRequirement::NeedExclusive,
        VulkanOp::ReadOnly => SyncRequirement::ThreadSafe,
        VulkanOp::QueueSubmit => SyncRequirement::NeedExclusive,
        VulkanOp::PoolScope => SyncRequirement::NeedExclusive,
    }
}

/// Whether a thread can perform an operation given the current registry.
pub open spec fn operation_permitted(
    reg: TokenRegistry,
    op: VulkanOp,
    object_id: nat,
    thread: ThreadId,
) -> bool {
    match sync_requirement(op) {
        SyncRequirement::NeedExclusive => {
            reg.tokens.contains_key(object_id)
            && reg.tokens[object_id].holder == Some(thread)
            && reg.tokens[object_id].access is Exclusive
        },
        SyncRequirement::ThreadSafe => {
            true
        },
        SyncRequirement::NeedExclusiveOrPoolOwner => {
            // Handled by pool_ownership module
            reg.tokens.contains_key(object_id)
            && reg.tokens[object_id].holder == Some(thread)
            && reg.tokens[object_id].access is Exclusive
        },
    }
}

/// No data race: an object is either exclusively owned, shared-read, or available.
pub open spec fn no_data_race(reg: TokenRegistry, object_id: nat) -> bool {
    reg.tokens.contains_key(object_id)
    && (
        // Exclusively owned by one thread
        (reg.tokens[object_id].access is Exclusive
         && reg.tokens[object_id].holder.is_some()
         && reg.tokens[object_id].shared_count == 0)
        // Shared by readers (no exclusive owner)
        || (reg.tokens[object_id].access is Shared
            && reg.tokens[object_id].holder.is_none())
        // Available (nobody accessing)
        || object_available(reg, object_id)
    )
}

/// A thread holds exclusive access to an object (convenience predicate).
pub open spec fn holds_exclusive(
    reg: TokenRegistry,
    object_id: nat,
    thread: ThreadId,
) -> bool {
    reg.tokens.contains_key(object_id)
    && reg.tokens[object_id].holder == Some(thread)
    && reg.tokens[object_id].access is Exclusive
}

/// No other thread holds exclusive access to an object.
pub open spec fn not_held_by_other(
    reg: TokenRegistry,
    object_id: nat,
    except: ThreadId,
) -> bool {
    !reg.tokens.contains_key(object_id)
    || reg.tokens[object_id].holder.is_none()
    || reg.tokens[object_id].holder == Some(except)
    || reg.tokens[object_id].access is Shared
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// After acquiring exclusive, the token is valid and the thread holds it.
pub proof fn lemma_acquire_exclusive_valid(
    reg: TokenRegistry,
    object_id: nat,
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

/// After acquiring exclusive, no data race exists.
pub proof fn lemma_acquire_exclusive_no_race(
    reg: TokenRegistry,
    object_id: nat,
    thread: ThreadId,
)
    requires object_available(reg, object_id),
    ensures ({
        let (new_reg, _) = acquire_exclusive(reg, object_id, thread);
        no_data_race(new_reg, object_id)
    }),
{
}

/// After releasing exclusive, the object is available.
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

/// Exclusive access blocks other threads.
pub proof fn lemma_exclusive_blocks_others(
    reg: TokenRegistry,
    object_id: nat,
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

/// Mutate operations require exclusive access.
pub proof fn lemma_mutate_requires_exclusive(
    reg: TokenRegistry,
    object_id: nat,
    thread: ThreadId,
)
    requires
        operation_permitted(reg, VulkanOp::Mutate, object_id, thread),
    ensures
        holds_exclusive(reg, object_id, thread),
{
}

/// Read-only operations are always permitted.
pub proof fn lemma_readonly_always_permitted(
    reg: TokenRegistry,
    object_id: nat,
    thread: ThreadId,
)
    ensures
        operation_permitted(reg, VulkanOp::ReadOnly, object_id, thread),
{
}

/// Acquiring/releasing doesn't affect other objects.
pub proof fn lemma_acquire_preserves_others(
    reg: TokenRegistry,
    object_id: nat,
    other_id: nat,
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

/// Release preserves other objects.
pub proof fn lemma_release_preserves_others(
    reg: TokenRegistry,
    token: SyncToken,
    other_id: nat,
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

/// Available object has no data race (trivially).
pub proof fn lemma_available_no_race(
    reg: TokenRegistry,
    object_id: nat,
)
    requires object_available(reg, object_id),
    ensures no_data_race(reg, object_id),
{
}

/// After acquiring shared, shared count increases.
pub proof fn lemma_acquire_shared_valid(
    reg: TokenRegistry,
    object_id: nat,
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

/// Shared access doesn't grant exclusive.
pub proof fn lemma_shared_not_exclusive(
    reg: TokenRegistry,
    object_id: nat,
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

/// Queue submit requires exclusive queue access.
pub proof fn lemma_submit_requires_exclusive(
    reg: TokenRegistry,
    queue_id: nat,
    thread: ThreadId,
)
    requires
        operation_permitted(reg, VulkanOp::QueueSubmit, queue_id, thread),
    ensures
        holds_exclusive(reg, queue_id, thread),
{
}

} // verus!
