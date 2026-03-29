use vstd::prelude::*;
use crate::mapped_buffer::*;
use crate::runtime::fence::RuntimeFence;

verus! {

///  Runtime wrapper for a persistently host-mapped GPU buffer.
///  Carries ghost ownership state that Verus checks at compile time.
pub struct RuntimeMappedBuffer {
    pub handle: u64,         //  VkBuffer handle
    pub mem_handle: u64,     //  VkDeviceMemory handle
    pub mapped_ptr: usize,   //  Persistently mapped host pointer (as usize for Verus)
    pub size: u64,           //  Buffer size in bytes
    pub state: Ghost<MappedBufferState>,
}

impl View for RuntimeMappedBuffer {
    type V = MappedBufferState;
    open spec fn view(&self) -> MappedBufferState { self.state@ }
}

///  Reclaim buffer ownership from GPU after fence wait.
///  The fence must be signaled (proved by prior vk_wait_for_fences call).
pub fn reclaim_buffer(buf: &mut RuntimeMappedBuffer, fence: &RuntimeFence)
    requires
        fence@.signaled,
        old(buf)@.ownership == BufferOwnership::GpuPending,
    ensures
        buf@.ownership == BufferOwnership::HostOwned,
        buf@.id == old(buf)@.id,
        buf@.size == old(buf)@.size,
        buf.handle == old(buf).handle,
        buf.mem_handle == old(buf).mem_handle,
        buf.mapped_ptr == old(buf).mapped_ptr,
        buf.size == old(buf).size,
{
    buf.state = Ghost(reclaim_ghost(buf.state@));
}

///  Release buffer to GPU before queue submit.
pub fn release_buffer(buf: &mut RuntimeMappedBuffer)
    requires
        old(buf)@.ownership == BufferOwnership::HostOwned,
    ensures
        buf@.ownership == BufferOwnership::GpuPending,
        buf@.id == old(buf)@.id,
        buf@.size == old(buf)@.size,
        buf.handle == old(buf).handle,
        buf.mem_handle == old(buf).mem_handle,
        buf.mapped_ptr == old(buf).mapped_ptr,
        buf.size == old(buf).size,
{
    buf.state = Ghost(release_ghost(buf.state@));
}

///  Write data to the mapped buffer at a given byte offset.
///  Requires HostOwned — the verifier rejects writes to GpuPending buffers.
#[verifier::external_body]
pub fn write_mapped_buffer(buf: &RuntimeMappedBuffer, src: &[u8], offset: usize)
    requires
        buf@.ownership == BufferOwnership::HostOwned,
        offset + src@.len() <= buf@.size,
{
    unsafe {
        std::ptr::copy_nonoverlapping(
            src.as_ptr(),
            (buf.mapped_ptr as *mut u8).add(offset),
            src.len(),
        );
    }
}

} //  verus!
