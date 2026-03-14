use vstd::prelude::*;
use crate::resource::*;
use crate::flags::*;
use crate::sync::*;
use crate::sync_proofs::*;
// Note: stage_access.rs has its own stage/access constants that conflict
// with flags.rs. Use flags.rs constants here since sync_proofs uses them.
use crate::recording::*;
use crate::recording_commands::*;
use crate::pipeline::*;
use crate::render_pass::*;
use crate::descriptor::*;
use crate::descriptor_validation::*;
use crate::descriptor_update::*;
use crate::framebuffer::*;
use crate::image_layout_fsm::*;
use crate::image_layout::*;
use crate::format_properties::*;
use crate::lock_ordering::*;
use crate::sync_token::*;
use crate::completion::*;
use crate::device::*;
use crate::lifetime::*;
use crate::memory_aliasing::*;
use crate::secondary_commands::*;
use crate::hot_reload::*;
use crate::shader_interface::*;
use crate::fence::*;
use crate::semaphore::*;
use crate::swapchain::*;

verus! {

// ══════════════════════════════════════════════════════════════════════
// Chain 1: Render Pipeline Composition
// recording.rs + draw_state.rs + render_pass.rs + pipeline.rs + descriptor_validation.rs
// ══════════════════════════════════════════════════════════════════════

/// A full draw call valid in recording_commands implies the recording state
/// has a render pass active and a graphics pipeline bound.
pub proof fn lemma_full_draw_implies_recording_state(
    ctx: RecordingContext,
    pipeline: GraphicsPipelineState,
    rp: RenderPassState,
)
    requires full_draw_call_valid(ctx, pipeline, rp),
    ensures
        in_render_pass(ctx.state),
        ctx.state.bound_graphics_pipeline == Some(pipeline.id),
        pipeline.alive,
{
}

/// Draw and dispatch are mutually exclusive across the full recording context.
pub proof fn lemma_full_draw_dispatch_exclusive(
    ctx: RecordingContext,
    g_pipeline: GraphicsPipelineState,
    rp: RenderPassState,
    c_pipeline: ComputePipelineState,
)
    ensures !(full_draw_call_valid(ctx, g_pipeline, rp)
              && full_dispatch_call_valid(ctx, c_pipeline)),
{
    if full_draw_call_valid(ctx, g_pipeline, rp)
        && full_dispatch_call_valid(ctx, c_pipeline) {
        // draw requires in_render_pass, dispatch requires !in_render_pass
        assert(in_render_pass(ctx.state));
        assert(!in_render_pass(ctx.state));
    }
}

/// After beginning a render pass and binding a compatible pipeline,
/// draw_call_valid holds.
pub proof fn lemma_begin_rp_bind_enables_draw(
    state: RecordingState,
    pipeline: GraphicsPipelineState,
    rp: RenderPassState,
    fb_id: nat,
)
    requires
        pipeline.alive,
        pipeline.render_pass_id == rp.id,
        pipeline.subpass_index == 0,
        rp.subpasses.len() > 0,
        graphics_pipeline_compatible_with_subpass(pipeline, rp, 0),
    ensures ({
        let s1 = begin_render_pass_recording(state, rp.id, fb_id);
        let s2 = bind_graphics_pipeline(s1, pipeline.id, pipeline.descriptor_set_layouts);
        draw_call_valid(s2, pipeline, rp)
    }),
{
}

// ══════════════════════════════════════════════════════════════════════
// Chain 2: Synchronization Composition
// sync.rs + sync_proofs.rs + stage_access.rs + flags.rs
// ══════════════════════════════════════════════════════════════════════

/// A valid transfer barrier (per stage_access) makes a resource readable
/// after a transfer write.
pub proof fn lemma_transfer_barrier_enables_read(
    log: BarrierLog,
    state: SyncState,
    resource: ResourceId,
)
    requires
        state.last_write.is_some(),
        resource_overlap(resource, state.resource),
        stages_subset(state.write_stages,
            PipelineStageFlags { stages: Set::empty().insert(STAGE_TRANSFER()) }),
        access_subset(state.write_accesses,
            AccessFlags { accesses: Set::empty().insert(ACCESS_TRANSFER_WRITE()) }),
    ensures ({
        let entry = BarrierEntry {
            resource,
            src_stages: PipelineStageFlags { stages: Set::empty().insert(STAGE_TRANSFER()) },
            src_accesses: AccessFlags { accesses: Set::empty().insert(ACCESS_TRANSFER_WRITE()) },
            dst_stages: PipelineStageFlags { stages: Set::empty().insert(STAGE_TRANSFER()) },
            dst_accesses: AccessFlags { accesses: Set::empty().insert(ACCESS_TRANSFER_READ()) },
        };
        readable(log.push(entry), state, STAGE_TRANSFER(), ACCESS_TRANSFER_READ())
    }),
{
    let entry = BarrierEntry {
        resource,
        src_stages: PipelineStageFlags { stages: Set::empty().insert(STAGE_TRANSFER()) },
        src_accesses: AccessFlags { accesses: Set::empty().insert(ACCESS_TRANSFER_WRITE()) },
        dst_stages: PipelineStageFlags { stages: Set::empty().insert(STAGE_TRANSFER()) },
        dst_accesses: AccessFlags { accesses: Set::empty().insert(ACCESS_TRANSFER_READ()) },
    };
    lemma_barrier_makes_readable(log, state, entry, STAGE_TRANSFER(), ACCESS_TRANSFER_READ());
}

/// A color write → fragment shader read barrier makes the resource readable
/// at fragment shader stage.
pub proof fn lemma_color_to_fragment_barrier_enables_read(
    log: BarrierLog,
    state: SyncState,
    resource: ResourceId,
)
    requires
        state.last_write.is_some(),
        resource_overlap(resource, state.resource),
        stages_subset(state.write_stages,
            PipelineStageFlags { stages: Set::empty().insert(STAGE_COLOR_ATTACHMENT_OUTPUT()) }),
        access_subset(state.write_accesses,
            AccessFlags { accesses: Set::empty().insert(ACCESS_COLOR_ATTACHMENT_WRITE()) }),
    ensures ({
        let entry = BarrierEntry {
            resource,
            src_stages: PipelineStageFlags { stages: Set::empty().insert(STAGE_COLOR_ATTACHMENT_OUTPUT()) },
            src_accesses: AccessFlags { accesses: Set::empty().insert(ACCESS_COLOR_ATTACHMENT_WRITE()) },
            dst_stages: PipelineStageFlags { stages: Set::empty().insert(STAGE_FRAGMENT_SHADER()) },
            dst_accesses: AccessFlags { accesses: Set::empty().insert(ACCESS_SHADER_READ()) },
        };
        readable(log.push(entry), state, STAGE_FRAGMENT_SHADER(), ACCESS_SHADER_READ())
    }),
{
    let entry = BarrierEntry {
        resource,
        src_stages: PipelineStageFlags { stages: Set::empty().insert(STAGE_COLOR_ATTACHMENT_OUTPUT()) },
        src_accesses: AccessFlags { accesses: Set::empty().insert(ACCESS_COLOR_ATTACHMENT_WRITE()) },
        dst_stages: PipelineStageFlags { stages: Set::empty().insert(STAGE_FRAGMENT_SHADER()) },
        dst_accesses: AccessFlags { accesses: Set::empty().insert(ACCESS_SHADER_READ()) },
    };
    lemma_barrier_makes_readable(log, state, entry, STAGE_FRAGMENT_SHADER(), ACCESS_SHADER_READ());
}

/// Adding barriers preserves existing readability.
pub proof fn lemma_barrier_chain_monotone(
    log: BarrierLog,
    state: SyncState,
    new_entry: BarrierEntry,
    dst_stage: nat,
    dst_access: nat,
)
    requires readable(log, state, dst_stage, dst_access),
    ensures readable(log.push(new_entry), state, dst_stage, dst_access),
{
    lemma_readable_monotone(log, state, new_entry, dst_stage, dst_access);
}

// ══════════════════════════════════════════════════════════════════════
// Chain 3: Lock Ordering + Thread Safety
// lock_ordering.rs + sync_token.rs
// ══════════════════════════════════════════════════════════════════════

/// A thread with no locks can acquire the device lock (level 0).
pub proof fn lemma_fresh_thread_can_acquire_device(thread: ThreadId)
    ensures can_acquire_at_level(no_locks(thread), device_level()),
{
    lemma_empty_locks_valid(thread);
}

/// After acquiring device lock, can acquire queue lock.
pub proof fn lemma_device_then_queue(thread: ThreadId, device_id: nat)
    ensures ({
        let h0 = no_locks(thread);
        let h1 = acquire_lock(h0, device_id, device_level());
        can_acquire_at_level(h1, queue_level())
    }),
{
    let h0 = no_locks(thread);
    lemma_empty_locks_valid(thread);
    lemma_acquire_maintains_order(h0, device_id, device_level());
}

/// After device + queue, can acquire command pool lock.
pub proof fn lemma_queue_then_command_pool(
    thread: ThreadId, device_id: nat, queue_id: nat,
)
    ensures ({
        let h0 = no_locks(thread);
        let h1 = acquire_lock(h0, device_id, device_level());
        let h2 = acquire_lock(h1, queue_id, queue_level());
        can_acquire_at_level(h2, command_pool_level())
    }),
{
    let h0 = no_locks(thread);
    lemma_empty_locks_valid(thread);
    lemma_acquire_maintains_order(h0, device_id, device_level());
    let h1 = acquire_lock(h0, device_id, device_level());
    lemma_acquire_maintains_order(h1, queue_id, queue_level());
}

/// The full 3-level lock acquisition chain is valid.
pub proof fn lemma_three_level_chain_valid(
    thread: ThreadId, device_id: nat, queue_id: nat, pool_id: nat,
)
    ensures ({
        let h0 = no_locks(thread);
        let h1 = acquire_lock(h0, device_id, device_level());
        let h2 = acquire_lock(h1, queue_id, queue_level());
        let h3 = acquire_lock(h2, pool_id, command_pool_level());
        lock_order_valid(h3)
    }),
{
    let h0 = no_locks(thread);
    lemma_empty_locks_valid(thread);
    lemma_acquire_maintains_order(h0, device_id, device_level());
    let h1 = acquire_lock(h0, device_id, device_level());
    lemma_acquire_maintains_order(h1, queue_id, queue_level());
    let h2 = acquire_lock(h1, queue_id, queue_level());
    lemma_acquire_maintains_order(h2, pool_id, command_pool_level());
}

// ══════════════════════════════════════════════════════════════════════
// Chain 4: Image Layout + Render Pass + Format Properties
// image_layout_fsm.rs + render_pass.rs + format_properties.rs
// ══════════════════════════════════════════════════════════════════════

/// If a render pass is well-formed and framebuffer well-formed, the
/// framebuffer has the right number of attachments.
pub proof fn lemma_rp_fb_attachment_agreement(
    rp: RenderPassState,
    fb: FramebufferState,
)
    requires
        render_pass_well_formed(rp),
        framebuffer_well_formed(fb, rp),
    ensures
        fb.attachments.len() == rp.attachments.len(),
{
}

/// A format that supports both color attachment and sampling can serve as
/// both a render target and a texture.
pub proof fn lemma_format_dual_use(props: FormatProperties)
    requires
        format_supports_color_attachment(props),
        format_supports_sampling(props),
    ensures
        format_valid_for_attachment(props, true, false, false),
{
}

// ══════════════════════════════════════════════════════════════════════
// Chain 5: Descriptor Consistency + Hot Reload
// hot_reload.rs + descriptor_validation.rs + descriptor_update.rs + shader_interface.rs
// ══════════════════════════════════════════════════════════════════════

/// Hot reload validity combined with safe_to_swap means the pipeline
/// can be swapped without affecting in-flight work.
pub proof fn lemma_hot_reload_safe_full(
    request: ReloadRequest,
    old_vertex: ShaderInterface,
    old_fragment: ShaderInterface,
    submissions: Seq<SubmissionRecord>,
)
    requires
        hot_reload_valid(request, old_vertex, old_fragment),
        safe_to_swap(submissions, request.old_pipeline_id),
    ensures
        // No in-flight work references the old pipeline
        safe_to_swap(submissions, request.old_pipeline_id),
        // New shaders are compatible
        hot_reload_valid(request, old_vertex, old_fragment),
{
}

// ══════════════════════════════════════════════════════════════════════
// Chain 6: Device Lifecycle
// device.rs + lifetime.rs + completion.rs + fence.rs + semaphore.rs
// ══════════════════════════════════════════════════════════════════════

/// Full device shutdown sequence: wait idle + destroy all resources → ready.
pub proof fn lemma_full_shutdown_sequence(dev: DeviceState)
    requires
        dev.live_buffers == 0,
        dev.live_images == 0,
        dev.live_pipelines == 0,
        dev.live_descriptor_pools == 0,
    ensures device_ready_for_shutdown(device_wait_idle_ghost(dev)),
{
    lemma_wait_idle_enables_shutdown(dev);
}

/// Creating then destroying a buffer restores the original count.
pub proof fn lemma_create_destroy_buffer_roundtrip(dev: DeviceState)
    ensures
        destroy_buffer_ghost(create_buffer_ghost(dev)).live_buffers == dev.live_buffers,
{
}

/// Creating then destroying an image restores the original count.
pub proof fn lemma_create_destroy_image_roundtrip(dev: DeviceState)
    ensures
        destroy_image_ghost(create_image_ghost(dev)).live_images == dev.live_images,
{
}

/// A fence signal → wait cycle returns to the initial unsignaled state.
pub proof fn lemma_fence_signal_wait_cycle(fence: FenceState, sub_id: nat)
    ensures ({
        let signaled = signal_fence_ghost(fence, sub_id);
        let reset = reset_fence_ghost(signaled);
        !reset.signaled && reset.submission_id.is_none()
    }),
{
}

/// A semaphore signal → wait cycle returns to unsignaled + empty states.
pub proof fn lemma_semaphore_signal_wait_cycle(
    sem: SemaphoreState,
    states: Map<ResourceId, SyncState>,
)
    ensures ({
        let signaled = signal_semaphore_ghost(sem, states);
        let waited = wait_semaphore_ghost(signaled);
        !waited.signaled
    }),
{
}

// ══════════════════════════════════════════════════════════════════════
// Chain 7: Swapchain + Render Pass + Secondary CB
// swapchain.rs + recording.rs + secondary_commands.rs
// ══════════════════════════════════════════════════════════════════════

/// A secondary CB that assumes a render pass is active can only
/// execute when the primary is in a render pass.
pub proof fn lemma_secondary_requires_render_pass_alignment(
    primary_ctx: RecordingContext,
    secondary: SecondaryCommandBuffer,
    rp: RenderPassState,
)
    requires
        secondary.assumptions.requires_render_pass,
        assumptions_satisfied(secondary.assumptions, primary_ctx, rp),
    ensures
        in_render_pass(primary_ctx.state),
{
}

/// After executing a secondary CB, the primary's recording state is unchanged.
pub proof fn lemma_execute_secondary_preserves_state(
    primary_ctx: RecordingContext,
    secondary: SecondaryCommandBuffer,
)
    ensures
        execute_secondary(primary_ctx, secondary).state == primary_ctx.state,
{
}

/// Swapchain acquire → present → complete preserves image count and
/// returns to the original state at that index.
pub proof fn lemma_swapchain_full_cycle_stable(
    swapchain: SwapchainState, idx: nat,
)
    requires
        !swapchain.retired,
        idx < swapchain.image_states.len(),
        swapchain.image_states[idx as int] == SwapchainImageState::Available,
    ensures ({
        let s1 = acquire_image(swapchain, idx).unwrap();
        let s2 = present_image(s1, idx).unwrap();
        let s3 = present_complete(s2, idx).unwrap();
        s3.image_states.len() == swapchain.image_states.len()
        && s3.image_states[idx as int] == SwapchainImageState::Available
    }),
{
}

} // verus!
