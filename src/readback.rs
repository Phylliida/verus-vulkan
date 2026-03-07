use vstd::prelude::*;
use crate::resource::*;
use crate::taint::*;
use crate::lifetime::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// Ghost model of buffer contents: a sequence of abstract data units.
///
/// The actual bytes are opaque — we track logical data identity, not
/// bit patterns. This is sufficient to prove that readback returns
/// the same data that was written.
pub struct BufferContents {
    /// Abstract data at each offset.
    pub data: Seq<nat>,
    /// Total size in abstract units.
    pub size: nat,
}

/// Ghost state for a staging buffer used for GPU↔CPU transfers.
pub struct StagingBufferState {
    /// Resource identifier.
    pub resource: ResourceId,
    /// Whether this buffer is host-visible (mappable).
    pub host_visible: bool,
    /// Whether this buffer is currently mapped.
    pub mapped: bool,
    /// Buffer size.
    pub size: nat,
    /// Current ghost contents.
    pub contents: BufferContents,
    /// Taint label (for information flow tracking).
    pub taint: TaintSet,
    /// Whether the buffer is alive.
    pub alive: bool,
}

/// Ghost state for a GPU-side buffer.
pub struct GpuBufferState {
    /// Resource identifier.
    pub resource: ResourceId,
    /// Buffer size.
    pub size: nat,
    /// Current ghost contents.
    pub contents: BufferContents,
    /// Taint label.
    pub taint: TaintSet,
    /// Whether the buffer is alive.
    pub alive: bool,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// Extract a slice of buffer contents.
pub open spec fn contents_slice(
    contents: BufferContents,
    offset: nat,
    size: nat,
) -> Seq<nat>
    recommends offset + size <= contents.size,
{
    contents.data.subrange(offset as int, (offset + size) as int)
}

/// A staging buffer is well-formed.
pub open spec fn staging_buffer_well_formed(buf: StagingBufferState) -> bool {
    buf.alive
    && buf.host_visible
    && buf.contents.size == buf.size
    && buf.contents.data.len() == buf.size
}

/// A GPU buffer is well-formed.
pub open spec fn gpu_buffer_well_formed(buf: GpuBufferState) -> bool {
    buf.alive
    && buf.contents.size == buf.size
    && buf.contents.data.len() == buf.size
}

/// Ghost update: copy from GPU buffer to staging buffer.
/// Models vkCmdCopyBuffer from a device-local buffer to a host-visible buffer.
pub open spec fn copy_to_staging_ghost(
    staging: StagingBufferState,
    gpu: GpuBufferState,
    src_offset: nat,
    dst_offset: nat,
    copy_size: nat,
) -> StagingBufferState
    recommends
        src_offset + copy_size <= gpu.size,
        dst_offset + copy_size <= staging.size,
{
    let new_data = Seq::new(
        staging.contents.data.len(),
        |i: int| {
            if dst_offset as int <= i < (dst_offset + copy_size) as int {
                gpu.contents.data[(src_offset as int) + (i - dst_offset as int)]
            } else {
                staging.contents.data[i]
            }
        },
    );
    StagingBufferState {
        contents: BufferContents {
            data: new_data,
            ..staging.contents
        },
        taint: TaintSet { labels: staging.taint.labels.union(gpu.taint.labels) },
        ..staging
    }
}

/// Ghost update: copy from host to GPU buffer.
/// Models the upload path (vkCmdCopyBuffer from staging to device-local).
pub open spec fn copy_from_staging_ghost(
    gpu: GpuBufferState,
    staging: StagingBufferState,
    src_offset: nat,
    dst_offset: nat,
    copy_size: nat,
) -> GpuBufferState
    recommends
        src_offset + copy_size <= staging.size,
        dst_offset + copy_size <= gpu.size,
{
    let new_data = Seq::new(
        gpu.contents.data.len(),
        |i: int| {
            if dst_offset as int <= i < (dst_offset + copy_size) as int {
                staging.contents.data[(src_offset as int) + (i - dst_offset as int)]
            } else {
                gpu.contents.data[i]
            }
        },
    );
    GpuBufferState {
        contents: BufferContents {
            data: new_data,
            ..gpu.contents
        },
        taint: TaintSet { labels: gpu.taint.labels.union(staging.taint.labels) },
        ..gpu
    }
}

/// No pending writes to a staging buffer: all submissions that reference
/// it have completed.
pub open spec fn no_pending_writes(
    submissions: Seq<SubmissionRecord>,
    resource: ResourceId,
) -> bool {
    no_pending_references(submissions, resource)
}

/// After a fence wait, the host can read the staging buffer.
pub open spec fn host_readable(
    submissions: Seq<SubmissionRecord>,
    staging: StagingBufferState,
) -> bool {
    staging.host_visible
    && staging.alive
    && no_pending_writes(submissions, staging.resource)
}

/// The staging buffer contents at a given region match the GPU buffer.
pub open spec fn staging_matches_gpu(
    staging: StagingBufferState,
    gpu: GpuBufferState,
    src_offset: nat,
    dst_offset: nat,
    copy_size: nat,
) -> bool
    recommends
        src_offset + copy_size <= gpu.size,
        dst_offset + copy_size <= staging.size,
{
    forall|i: int| dst_offset as int <= i < (dst_offset + copy_size) as int
        ==> staging.contents.data[i]
            == gpu.contents.data[(src_offset as int) + (i - dst_offset as int)]
}

/// A full readback is valid: copy, fence wait, then map.
pub open spec fn readback_valid(
    submissions: Seq<SubmissionRecord>,
    staging: StagingBufferState,
    gpu: GpuBufferState,
    src_offset: nat,
    dst_offset: nat,
    copy_size: nat,
) -> bool {
    staging_matches_gpu(staging, gpu, src_offset, dst_offset, copy_size)
    && host_readable(submissions, staging)
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// After copy_to_staging_ghost, the staging buffer contents match the GPU source.
pub proof fn lemma_copy_preserves_contents(
    staging: StagingBufferState,
    gpu: GpuBufferState,
    src_offset: nat,
    dst_offset: nat,
    copy_size: nat,
)
    requires
        staging_buffer_well_formed(staging),
        gpu_buffer_well_formed(gpu),
        src_offset + copy_size <= gpu.size,
        dst_offset + copy_size <= staging.size,
    ensures
        staging_matches_gpu(
            copy_to_staging_ghost(staging, gpu, src_offset, dst_offset, copy_size),
            gpu,
            src_offset,
            dst_offset,
            copy_size,
        ),
{
    let result = copy_to_staging_ghost(staging, gpu, src_offset, dst_offset, copy_size);
    assert forall|i: int| dst_offset as int <= i < (dst_offset + copy_size) as int
    implies result.contents.data[i]
        == gpu.contents.data[(src_offset as int) + (i - dst_offset as int)] by {
        // Direct from Seq::new definition
    }
}

/// Copy does not affect regions outside the copy range.
pub proof fn lemma_copy_preserves_outside(
    staging: StagingBufferState,
    gpu: GpuBufferState,
    src_offset: nat,
    dst_offset: nat,
    copy_size: nat,
    idx: int,
)
    requires
        staging_buffer_well_formed(staging),
        gpu_buffer_well_formed(gpu),
        src_offset + copy_size <= gpu.size,
        dst_offset + copy_size <= staging.size,
        0 <= idx < staging.size as int,
        !(dst_offset as int <= idx < (dst_offset + copy_size) as int),
    ensures
        copy_to_staging_ghost(staging, gpu, src_offset, dst_offset, copy_size)
            .contents.data[idx] == staging.contents.data[idx],
{
}

/// Copy preserves the staging buffer's host_visible and alive flags.
pub proof fn lemma_copy_preserves_staging_metadata(
    staging: StagingBufferState,
    gpu: GpuBufferState,
    src_offset: nat,
    dst_offset: nat,
    copy_size: nat,
)
    requires
        src_offset + copy_size <= gpu.size,
        dst_offset + copy_size <= staging.size,
    ensures ({
        let result = copy_to_staging_ghost(staging, gpu, src_offset, dst_offset, copy_size);
        result.host_visible == staging.host_visible
        && result.alive == staging.alive
        && result.resource == staging.resource
        && result.size == staging.size
    }),
{
}

/// Taint flows through copy: the result taint is the union of both buffers.
pub proof fn lemma_copy_propagates_taint(
    staging: StagingBufferState,
    gpu: GpuBufferState,
    src_offset: nat,
    dst_offset: nat,
    copy_size: nat,
)
    requires
        src_offset + copy_size <= gpu.size,
        dst_offset + copy_size <= staging.size,
    ensures
        copy_to_staging_ghost(staging, gpu, src_offset, dst_offset, copy_size)
            .taint == (TaintSet { labels: staging.taint.labels.union(gpu.taint.labels) }),
{
}

/// A round-trip upload then readback recovers the original data.
/// write to staging → copy to GPU → copy back to staging → data matches.
pub proof fn lemma_roundtrip_preserves_data(
    staging: StagingBufferState,
    gpu: GpuBufferState,
    offset: nat,
    copy_size: nat,
)
    requires
        staging_buffer_well_formed(staging),
        gpu_buffer_well_formed(gpu),
        offset + copy_size <= staging.size,
        offset + copy_size <= gpu.size,
    ensures ({
        // Upload: staging → gpu
        let gpu_after_upload = copy_from_staging_ghost(gpu, staging, offset, offset, copy_size);
        // Readback: gpu → staging (into same location)
        let staging_after_readback = copy_to_staging_ghost(staging, gpu_after_upload, offset, offset, copy_size);
        // Data matches the original staging contents
        forall|i: int| offset as int <= i < (offset + copy_size) as int
            ==> staging_after_readback.contents.data[i] == staging.contents.data[i]
    }),
{
    let gpu_after_upload = copy_from_staging_ghost(gpu, staging, offset, offset, copy_size);
    let staging_after_readback = copy_to_staging_ghost(staging, gpu_after_upload, offset, offset, copy_size);

    assert forall|i: int| offset as int <= i < (offset + copy_size) as int
    implies staging_after_readback.contents.data[i] == staging.contents.data[i] by {
        // staging_after_readback.contents.data[i]
        //   = gpu_after_upload.contents.data[offset + (i - offset)]    (from copy_to_staging)
        //   = gpu_after_upload.contents.data[i]
        //   = staging.contents.data[offset + (i - offset)]             (from copy_from_staging)
        //   = staging.contents.data[i]
        assert(staging_after_readback.contents.data[i]
            == gpu_after_upload.contents.data[(offset as int) + (i - offset as int)]);
        assert(gpu_after_upload.contents.data[(offset as int) + (i - offset as int)]
            == staging.contents.data[(offset as int) + ((offset as int) + (i - offset as int) - offset as int)]);
    }
}

/// An empty submission log means the staging buffer is host-readable.
pub proof fn lemma_empty_submissions_host_readable(
    staging: StagingBufferState,
)
    requires
        staging.host_visible,
        staging.alive,
    ensures
        host_readable(Seq::<SubmissionRecord>::empty(), staging),
{
}

/// Copy to staging preserves well-formedness.
pub proof fn lemma_copy_preserves_staging_well_formed(
    staging: StagingBufferState,
    gpu: GpuBufferState,
    src_offset: nat,
    dst_offset: nat,
    copy_size: nat,
)
    requires
        staging_buffer_well_formed(staging),
        gpu_buffer_well_formed(gpu),
        src_offset + copy_size <= gpu.size,
        dst_offset + copy_size <= staging.size,
    ensures
        staging_buffer_well_formed(
            copy_to_staging_ghost(staging, gpu, src_offset, dst_offset, copy_size)
        ),
{
    let result = copy_to_staging_ghost(staging, gpu, src_offset, dst_offset, copy_size);
    assert(result.contents.data.len() == staging.size);
}

} // verus!
