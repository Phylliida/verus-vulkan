use vstd::prelude::*;
use crate::memory::*;
use crate::resource::*;
use crate::memory_aliasing::*;
use crate::sync_token::*;

verus! {

/// Runtime wrapper for a VkDeviceMemory allocation.
pub struct RuntimeAllocation {
    /// Opaque handle (maps to VkDeviceMemory).
    pub handle: u64,
    /// Ghost model of the allocation.
    pub state: Ghost<MemoryAllocation>,
    /// Whether this allocation is currently mapped.
    pub mapped: Ghost<bool>,
}

impl View for RuntimeAllocation {
    type V = MemoryAllocation;
    open spec fn view(&self) -> MemoryAllocation { self.state@ }
}

/// Well-formedness of the runtime allocation.
pub open spec fn runtime_alloc_wf(alloc: &RuntimeAllocation) -> bool {
    alloc@.alive
}

/// Exec: allocate memory.
pub fn allocate_exec(
    id: Ghost<nat>,
    heap_index: Ghost<nat>,
    size: Ghost<nat>,
) -> (out: RuntimeAllocation)
    ensures
        out@.id == id@,
        out@.heap_index == heap_index@,
        out@.size == size@,
        out@.alive,
        out.mapped@ == false,
{
    RuntimeAllocation {
        handle: 0,
        state: Ghost(MemoryAllocation {
            id: id@,
            heap_index: heap_index@,
            size: size@,
            alive: true,
        }),
        mapped: Ghost(false),
    }
}

/// Exec: free memory.
/// Caller must prove no resource is still bound to this allocation and exclusive access.
pub fn free_exec(
    alloc: &mut RuntimeAllocation,
    resource_bindings: Ghost<Map<ResourceId, MemoryRange>>,
    thread: Ghost<ThreadId>,
    reg: Ghost<TokenRegistry>,
)
    requires
        runtime_alloc_wf(&*old(alloc)),
        old(alloc).mapped@ == false,
        no_resources_use_allocation(resource_bindings@, old(alloc)@.id),
        holds_exclusive(reg@, SyncObjectId::Handle(old(alloc)@.id), thread@),
    ensures
        !alloc@.alive,
        alloc@.id == old(alloc)@.id,
{
    alloc.state = Ghost(MemoryAllocation {
        alive: false,
        ..alloc.state@
    });
}

/// Exec: map memory (marks as mapped).
/// Caller must prove exclusive access to the memory object.
pub fn map_memory_exec(
    alloc: &mut RuntimeAllocation,
    thread: Ghost<ThreadId>,
    reg: Ghost<TokenRegistry>,
)
    requires
        runtime_alloc_wf(&*old(alloc)),
        old(alloc).mapped@ == false,
        holds_exclusive(reg@, SyncObjectId::Handle(old(alloc)@.id), thread@),
    ensures
        alloc.mapped@ == true,
        alloc@ == old(alloc)@,
{
    alloc.mapped = Ghost(true);
}

/// Exec: unmap memory.
/// Caller must prove exclusive access to the memory object.
pub fn unmap_memory_exec(
    alloc: &mut RuntimeAllocation,
    thread: Ghost<ThreadId>,
    reg: Ghost<TokenRegistry>,
)
    requires
        runtime_alloc_wf(&*old(alloc)),
        old(alloc).mapped@ == true,
        holds_exclusive(reg@, SyncObjectId::Handle(old(alloc)@.id), thread@),
    ensures
        alloc.mapped@ == false,
        alloc@ == old(alloc)@,
{
    alloc.mapped = Ghost(false);
}

// ── Extended Specs & Proofs ──────────────────────────────────────────

/// Allocation is alive.
pub open spec fn alloc_alive(alloc: &RuntimeAllocation) -> bool {
    alloc@.alive
}

/// Allocation is mapped.
pub open spec fn alloc_is_mapped(alloc: &RuntimeAllocation) -> bool {
    alloc.mapped@
}

/// Allocation ID.
pub open spec fn alloc_id(alloc: &RuntimeAllocation) -> nat {
    alloc@.id
}

/// Allocation size.
pub open spec fn alloc_size(alloc: &RuntimeAllocation) -> nat {
    alloc@.size
}

/// Proof: a new allocation is alive and unmapped.
pub proof fn lemma_new_alloc_alive_unmapped(
    id: Ghost<nat>,
    heap_index: Ghost<nat>,
    size: Ghost<nat>,
)
    ensures ({
        let out = RuntimeAllocation {
            handle: 0,
            state: Ghost(MemoryAllocation {
                id: id@, heap_index: heap_index@, size: size@, alive: true,
            }),
            mapped: Ghost(false),
        };
        alloc_alive(&out) && !alloc_is_mapped(&out)
    }),
{
}

/// Proof: freed allocation is not alive.
pub proof fn lemma_freed_not_alive(alloc: &RuntimeAllocation)
    requires
        runtime_alloc_wf(alloc),
        alloc.mapped@ == false,
    ensures ({
        let freed_state = MemoryAllocation { alive: false, ..alloc@ };
        !freed_state.alive
    }),
{
}

/// Proof: mapping preserves alive status.
pub proof fn lemma_map_preserves_alive(alloc: &RuntimeAllocation)
    requires runtime_alloc_wf(alloc),
    ensures alloc@.alive,
{
}

/// Proof: unmapping preserves alive status.
pub proof fn lemma_unmap_preserves_alive(alloc: &RuntimeAllocation)
    requires runtime_alloc_wf(alloc),
    ensures alloc@.alive,
{
}

} // verus!
