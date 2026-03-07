use vstd::prelude::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// Thread identifier.
pub type ThreadId = nat;

/// The kind of Vulkan object, determining its synchronization requirements.
/// Per the Vulkan spec, most objects are "externally synchronized" —
/// only one thread may access them at a time.
pub enum VulkanObjectKind {
    /// VkQueue — externally synchronized per queue.
    Queue,
    /// VkCommandBuffer — externally synchronized per CB.
    CommandBuffer,
    /// VkCommandPool — externally synchronized; covers all CBs from this pool.
    CommandPool,
    /// VkDescriptorPool — externally synchronized per pool.
    DescriptorPool,
    /// VkDevice — some operations require external sync on the device.
    Device,
    /// VkFence — externally synchronized.
    Fence,
    /// VkSemaphore — externally synchronized for signal/wait.
    Semaphore,
    /// VkPipeline — thread-safe for use, externally synchronized for destroy.
    Pipeline,
    /// VkSwapchain — externally synchronized.
    Swapchain,
}

/// Access mode: shared (read-only) or exclusive (read-write).
pub enum AccessMode {
    /// Multiple threads can hold shared access simultaneously.
    Shared,
    /// Only one thread can hold exclusive access.
    Exclusive,
}

/// Ownership of a Vulkan object: which thread currently has access.
pub struct ObjectOwnership {
    /// The object's unique id.
    pub object_id: nat,
    /// The kind of Vulkan object.
    pub kind: VulkanObjectKind,
    /// Current owning thread (None = unowned / available).
    pub owner: Option<ThreadId>,
    /// Current access mode.
    pub access_mode: AccessMode,
    /// Number of shared readers (valid when access_mode == Shared).
    pub shared_count: nat,
}

/// Full thread-safety state: tracks ownership of all objects.
pub struct ThreadSafetyState {
    /// Ownership state of each object.
    pub objects: Map<nat, ObjectOwnership>,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// An object is available (not owned by any thread).
pub open spec fn object_available(state: ThreadSafetyState, object_id: nat) -> bool {
    state.objects.contains_key(object_id)
    && state.objects[object_id].owner.is_none()
    && state.objects[object_id].shared_count == 0
}

/// A thread has exclusive access to an object.
pub open spec fn has_exclusive_access(
    state: ThreadSafetyState,
    object_id: nat,
    thread: ThreadId,
) -> bool {
    state.objects.contains_key(object_id)
    && state.objects[object_id].owner == Some(thread)
    && state.objects[object_id].access_mode == AccessMode::Exclusive
}

/// A thread has shared access to an object.
pub open spec fn has_shared_access(
    state: ThreadSafetyState,
    object_id: nat,
    thread: ThreadId,
) -> bool {
    state.objects.contains_key(object_id)
    && state.objects[object_id].access_mode == AccessMode::Shared
    && state.objects[object_id].shared_count > 0
}

/// Acquire exclusive access to an object.
pub open spec fn acquire_exclusive(
    state: ThreadSafetyState,
    object_id: nat,
    thread: ThreadId,
) -> ThreadSafetyState
    recommends object_available(state, object_id),
{
    ThreadSafetyState {
        objects: state.objects.insert(object_id, ObjectOwnership {
            owner: Some(thread),
            access_mode: AccessMode::Exclusive,
            shared_count: 0,
            ..state.objects[object_id]
        }),
    }
}

/// Release exclusive access to an object.
pub open spec fn release_exclusive(
    state: ThreadSafetyState,
    object_id: nat,
) -> ThreadSafetyState
    recommends state.objects.contains_key(object_id),
{
    ThreadSafetyState {
        objects: state.objects.insert(object_id, ObjectOwnership {
            owner: None,
            access_mode: AccessMode::Shared,
            shared_count: 0,
            ..state.objects[object_id]
        }),
    }
}

/// Acquire shared access.
pub open spec fn acquire_shared(
    state: ThreadSafetyState,
    object_id: nat,
    thread: ThreadId,
) -> ThreadSafetyState
    recommends state.objects.contains_key(object_id),
{
    let obj = state.objects[object_id];
    ThreadSafetyState {
        objects: state.objects.insert(object_id, ObjectOwnership {
            access_mode: AccessMode::Shared,
            shared_count: obj.shared_count + 1,
            ..obj
        }),
    }
}

/// Release shared access.
pub open spec fn release_shared(
    state: ThreadSafetyState,
    object_id: nat,
) -> ThreadSafetyState
    recommends
        state.objects.contains_key(object_id),
        state.objects[object_id].shared_count > 0,
{
    let obj = state.objects[object_id];
    let new_count = (obj.shared_count - 1) as nat;
    ThreadSafetyState {
        objects: state.objects.insert(object_id, ObjectOwnership {
            shared_count: new_count,
            owner: if new_count == 0 { None } else { obj.owner },
            ..obj
        }),
    }
}

/// Exclusive acquisition is valid: object must be available.
pub open spec fn can_acquire_exclusive(
    state: ThreadSafetyState,
    object_id: nat,
) -> bool {
    object_available(state, object_id)
}

/// Shared acquisition is valid: no exclusive owner.
pub open spec fn can_acquire_shared(
    state: ThreadSafetyState,
    object_id: nat,
) -> bool {
    state.objects.contains_key(object_id)
    && (state.objects[object_id].access_mode == AccessMode::Shared
        || object_available(state, object_id))
}

/// An object that requires external synchronization is properly
/// synchronized: exactly one thread has exclusive access during mutation.
pub open spec fn externally_synchronized(
    state: ThreadSafetyState,
    object_id: nat,
    thread: ThreadId,
) -> bool {
    has_exclusive_access(state, object_id, thread)
}

/// No data race: an object is either exclusively owned by one thread,
/// or shared by multiple readers (but no writer).
pub open spec fn no_data_race(state: ThreadSafetyState, object_id: nat) -> bool {
    state.objects.contains_key(object_id)
    && (
        // Case 1: exclusively owned by exactly one thread
        (state.objects[object_id].access_mode == AccessMode::Exclusive
         && state.objects[object_id].owner.is_some()
         && state.objects[object_id].shared_count == 0)
        // Case 2: shared by readers (no exclusive owner)
        || (state.objects[object_id].access_mode == AccessMode::Shared
            && state.objects[object_id].owner.is_none())
        // Case 3: available (no one accessing)
        || object_available(state, object_id)
    )
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// After acquiring exclusive access, the thread has exclusive access.
pub proof fn lemma_acquire_exclusive_grants_access(
    state: ThreadSafetyState,
    object_id: nat,
    thread: ThreadId,
)
    requires object_available(state, object_id),
    ensures
        has_exclusive_access(
            acquire_exclusive(state, object_id, thread),
            object_id,
            thread,
        ),
{
}

/// After acquiring exclusive access, the object has no data race.
pub proof fn lemma_acquire_exclusive_no_race(
    state: ThreadSafetyState,
    object_id: nat,
    thread: ThreadId,
)
    requires object_available(state, object_id),
    ensures
        no_data_race(acquire_exclusive(state, object_id, thread), object_id),
{
}

/// After releasing exclusive access, the object is available.
pub proof fn lemma_release_makes_available(
    state: ThreadSafetyState,
    object_id: nat,
)
    requires state.objects.contains_key(object_id),
    ensures
        object_available(release_exclusive(state, object_id), object_id),
{
}

/// Exclusive access prevents other threads from accessing.
pub proof fn lemma_exclusive_blocks_others(
    state: ThreadSafetyState,
    object_id: nat,
    owner: ThreadId,
    other: ThreadId,
)
    requires
        has_exclusive_access(state, object_id, owner),
        owner != other,
    ensures
        !has_exclusive_access(state, object_id, other),
{
}

/// Available object has no data race (trivially).
pub proof fn lemma_available_no_race(
    state: ThreadSafetyState,
    object_id: nat,
)
    requires object_available(state, object_id),
    ensures no_data_race(state, object_id),
{
}

/// Acquiring/releasing doesn't affect other objects.
pub proof fn lemma_acquire_preserves_others(
    state: ThreadSafetyState,
    object_id: nat,
    other_id: nat,
    thread: ThreadId,
)
    requires
        object_available(state, object_id),
        other_id != object_id,
        state.objects.contains_key(other_id),
    ensures
        acquire_exclusive(state, object_id, thread)
            .objects[other_id] == state.objects[other_id],
{
}

} // verus!
