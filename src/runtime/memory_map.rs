use vstd::prelude::*;
use crate::memory_map::*;
use crate::resource::*;
use crate::runtime::device::*;

verus! {

/// Runtime wrapper for memory map tracking state.
pub struct RuntimeMemoryMap {
    /// Ghost model of the memory map state.
    pub state: Ghost<MemoryMapState>,
}

impl View for RuntimeMemoryMap {
    type V = MemoryMapState;
    open spec fn view(&self) -> MemoryMapState { self.state@ }
}

/// Exec: create a memory map tracker from ghost state.
pub fn create_memory_map_exec(
    mm_state: Ghost<MemoryMapState>,
) -> (out: RuntimeMemoryMap)
    ensures out@ == mm_state@,
{
    RuntimeMemoryMap { state: mm_state }
}

/// Exec: map memory for host access.
pub fn map_exec(
    mm: &mut RuntimeMemoryMap,
    offset: Ghost<nat>,
    size: Ghost<nat>,
)
    requires can_map(old(mm)@),
    ensures
        mm@ == map_memory(old(mm)@, offset@, size@),
        mm@.mapped,
{
    mm.state = Ghost(map_memory(mm.state@, offset@, size@));
}

/// Exec: unmap memory.
pub fn unmap_exec(mm: &mut RuntimeMemoryMap)
    requires old(mm)@.mapped,
    ensures
        mm@ == unmap_memory(old(mm)@),
        !mm@.mapped,
{
    mm.state = Ghost(unmap_memory(mm.state@));
}

/// Exec: host write to mapped memory.
/// Caller must prove the GPU has no pending references to this resource.
pub fn host_write_exec(
    mm: &mut RuntimeMemoryMap,
    dev: &RuntimeDevice,
    resource: Ghost<ResourceId>,
)
    requires
        old(mm)@.mapped,
        host_writable(dev@.pending_submissions, resource@),
    ensures
        mm@ == host_write(old(mm)@),
{
    mm.state = Ghost(host_write(mm.state@));
}

/// Exec: flush mapped memory range.
pub fn flush_exec(mm: &mut RuntimeMemoryMap)
    requires old(mm)@.mapped,
    ensures
        mm@ == flush_memory(old(mm)@),
        host_writes_visible(mm@),
{
    mm.state = Ghost(flush_memory(mm.state@));
}

/// Exec: invalidate mapped memory range.
pub fn invalidate_exec(mm: &mut RuntimeMemoryMap)
    requires old(mm)@.mapped,
    ensures
        mm@ == invalidate_memory(old(mm)@),
        host_read_safe(mm@),
{
    mm.state = Ghost(invalidate_memory(mm.state@));
}

} // verus!
