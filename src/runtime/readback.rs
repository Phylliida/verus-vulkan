use vstd::prelude::*;
use crate::readback::*;
use crate::resource::*;
use crate::taint::*;

verus! {

///  Runtime wrapper for a staging buffer (host-visible, used for GPU↔CPU transfers).
pub struct RuntimeStagingBuffer {
    ///  Ghost model of the staging buffer state.
    pub state: Ghost<StagingBufferState>,
}

impl View for RuntimeStagingBuffer {
    type V = StagingBufferState;
    open spec fn view(&self) -> StagingBufferState { self.state@ }
}

///  Well-formedness of the runtime staging buffer.
pub open spec fn runtime_staging_wf(buf: &RuntimeStagingBuffer) -> bool {
    staging_buffer_well_formed(buf@)
}

///  Runtime wrapper for a GPU-side buffer.
pub struct RuntimeGpuBuffer {
    ///  Ghost model of the GPU buffer state.
    pub state: Ghost<GpuBufferState>,
}

impl View for RuntimeGpuBuffer {
    type V = GpuBufferState;
    open spec fn view(&self) -> GpuBufferState { self.state@ }
}

///  Well-formedness of the runtime GPU buffer.
pub open spec fn runtime_gpu_wf(buf: &RuntimeGpuBuffer) -> bool {
    gpu_buffer_well_formed(buf@)
}

///  Exec: create a staging buffer from ghost state.
pub fn create_staging_buffer_exec(
    staging_state: Ghost<StagingBufferState>,
) -> (out: RuntimeStagingBuffer)
    requires staging_buffer_well_formed(staging_state@),
    ensures
        out@ == staging_state@,
        runtime_staging_wf(&out),
{
    RuntimeStagingBuffer { state: staging_state }
}

///  Exec: create a GPU buffer from ghost state.
pub fn create_gpu_buffer_exec(
    gpu_state: Ghost<GpuBufferState>,
) -> (out: RuntimeGpuBuffer)
    requires gpu_buffer_well_formed(gpu_state@),
    ensures
        out@ == gpu_state@,
        runtime_gpu_wf(&out),
{
    RuntimeGpuBuffer { state: gpu_state }
}

///  Exec: copy from GPU buffer to staging buffer (readback).
pub fn copy_to_staging_exec(
    staging: &mut RuntimeStagingBuffer,
    gpu: &RuntimeGpuBuffer,
    src_offset: Ghost<nat>,
    dst_offset: Ghost<nat>,
    copy_size: Ghost<nat>,
)
    requires
        runtime_staging_wf(&*old(staging)),
        runtime_gpu_wf(gpu),
        src_offset@ + copy_size@ <= gpu@.size,
        dst_offset@ + copy_size@ <= old(staging)@.size,
    ensures
        staging@ == copy_to_staging_ghost(old(staging)@, gpu@, src_offset@, dst_offset@, copy_size@),
        runtime_staging_wf(staging),
{
    proof {
        lemma_copy_preserves_staging_well_formed(
            staging.state@, gpu.state@, src_offset@, dst_offset@, copy_size@,
        );
    }
    staging.state = Ghost(copy_to_staging_ghost(
        staging.state@, gpu.state@, src_offset@, dst_offset@, copy_size@,
    ));
}

///  Exec: copy from staging buffer to GPU buffer (upload).
pub fn copy_from_staging_exec(
    gpu: &mut RuntimeGpuBuffer,
    staging: &RuntimeStagingBuffer,
    src_offset: Ghost<nat>,
    dst_offset: Ghost<nat>,
    copy_size: Ghost<nat>,
)
    requires
        runtime_gpu_wf(&*old(gpu)),
        runtime_staging_wf(staging),
        src_offset@ + copy_size@ <= staging@.size,
        dst_offset@ + copy_size@ <= old(gpu)@.size,
    ensures
        gpu@ == copy_from_staging_ghost(old(gpu)@, staging@, src_offset@, dst_offset@, copy_size@),
{
    gpu.state = Ghost(copy_from_staging_ghost(
        gpu.state@, staging.state@, src_offset@, dst_offset@, copy_size@,
    ));
}

} //  verus!
