# Caldera: A Formally Verified Vulkan Rendering Layer

## Design Document v0.4

---

## 1. Name

**Caldera** — a massive volcanic formation that contains and shapes the power within it. Vulkan is the Roman god of fire and the forge; a caldera is the geological structure that constrains volcanic force into a stable, bounded form. The metaphor is the project's thesis: Vulkan is immensely powerful but riddled with undefined behavior at every wrong step, and Caldera's purpose is to contain that power within formally verified boundaries so that it can be wielded safely. The name is short, memorable, and `caldera` is available as a crate name prefix.

---

## 2. Executive Summary

Caldera is a Rust library that wraps the Vulkan graphics API with formal verification of API usage correctness via Verus. Every Vulkan object carries ghost-level metadata describing its creation parameters, current state, and synchronization history. Every Vulkan command is gated by Verus preconditions that encode the Vulkan specification's validity requirements. The result is that a program which passes Verus verification is guaranteed — modulo driver bugs and hardware faults — to never trigger Vulkan undefined behavior.

The primary application target is real-time social VR rendering, where the consequences of GPU faults are not merely visual artifacts but physical discomfort. A dropped frame, a synchronization race that corrupts a stereo pair, or a pipeline barrier omission that produces a single garbled frame every few minutes — these are the bugs that Caldera exists to prevent. The library integrates with CuTe-RS for verified compute workloads, creating a stack where both the compute kernels and the command submission layer are formally verified.

Caldera is not a rendering engine. It is not a scene graph, an ECS, or a material system. It is a thin, verified abstraction over Vulkan's command recording and resource management APIs. A rendering engine would be built on top of it, and that engine would inherit Caldera's compile-time correctness guarantees without needing to reason about Vulkan validity rules directly.

---

## 3. Goals and Non-Goals

Caldera's verification ambition goes beyond "no undefined behavior." Preventing UB is the floor, not the ceiling. Verus enables a hierarchy of compile-time guarantees, from basic API safety up through resource management correctness and architectural invariants:

**Level 1 — No Vulkan undefined behavior.** Encode the Vulkan specification's validity requirements as Verus preconditions on Rust wrapper functions, so that invalid API usage is a static verification failure. This covers synchronization hazards, image layout violations, descriptor mismatches, and bounds errors.

**Level 2 — Resource lifecycle correctness.** Track every GPU resource from creation to destruction. Prove that no resource is used after destruction (use-after-free), no resource is destroyed while in-flight (dangling reference), no resource is leaked (memory exhaustion), and total GPU memory stays within device limits (budget enforcement).

**Level 3 — Protocol correctness.** Verify that multi-step protocols are followed completely. The swapchain acquire→render→present cycle completes without deadlock. Secondary command buffers are only executed when their recorded assumptions still hold. Descriptor sets match their pipeline layouts at every draw call.

**Level 4 — Architectural invariants.** Verify higher-level properties of the rendering pipeline. A render graph DAG is acyclic and all dependencies are satisfied. Every VR frame renders both eyes before presentation. Stereo renders use consistent scene data across eyes. Reprojection metadata (depth, motion vectors) is always present.

**Level 5 — Data integrity across the full pipeline.** Verify that asset data (meshes, textures) satisfies structural invariants before GPU upload. Verify that GPU readback produces exactly what the GPU wrote. Thread ghost invariants across crate boundaries — from verus-topology mesh construction through CuTe-RS compute through Caldera rendering — so a topology bug surfaces as a verification error at the draw call that consumes it.

**Level 6 — Information flow and temporal properties.** Track ghost taint labels on GPU buffers to prove that private data (player hand tracking, eye gaze) never renders on another player's screen. Verify multi-frame loop invariants: memory stability, animation continuity, ring buffer correctness. Verify that shader hot-reload preserves all pipeline compatibility invariants. When CuTe-RS kernels provide functional specifications, thread those specs through Caldera's command model for end-to-end correctness.

All six levels impose zero runtime overhead — the verified wrappers compile down to the same `ash` FFI calls that hand-written Vulkan code would make, with all ghost state erased.

The project does not aim to cover the entire Vulkan specification from day one. The initial scope is the subset needed for a stereoscopic VR rendering pipeline: instance and device creation, swapchain management, render passes with color and depth attachments, graphics and compute pipelines, descriptor sets, buffer and image management, command buffer recording, synchronization (fences, semaphores, pipeline barriers), and presentation. Extensions like ray tracing, video decode, mesh shading, and sparse resources are deferred. The project does not aim to verify the Vulkan driver or GPU hardware — these are in the trusted computing base. The project does not aim to verify shader correctness at the SPIR-V level (CuTe-RS handles compute shader verification; graphics shader verification is a separate research problem). The project does not aim to be a high-level rendering framework — it is infrastructure for building one.

---

## 4. Background: Why Vulkan Needs Verification

Vulkan's explicit design philosophy places the burden of correctness entirely on the application. Unlike OpenGL, which silently handled resource transitions, synchronization, and memory management, Vulkan requires the programmer to specify every pipeline barrier, every image layout transition, every queue ownership transfer, every memory allocation and binding. The Vulkan specification contains over 800 "Valid Usage" rules for the core API alone, each of which, if violated, produces undefined behavior — not an error code, not a crash, but arbitrary GPU behavior including silent corruption, device loss, or driver-level hangs.

The Vulkan validation layers (VK_LAYER_KHRONOS_validation) catch many of these violations at runtime, but they have fundamental limitations. They can only check the code paths that are actually executed, they have false negatives for race conditions and synchronization errors (especially cross-queue), they impose significant runtime overhead that makes them unsuitable for production VR where every millisecond matters, and they provide error messages after the fact rather than preventing the error from being authored in the first place.

Existing Rust Vulkan wrappers (vulkano, wgpu) provide varying degrees of safety. Vulkano checks many validity rules at runtime, adding overhead and turning undefined behavior into panics — better, but still a runtime failure. wgpu provides a safe high-level API but does so by restricting what you can express, which limits performance for demanding VR workloads. Neither provides static, compile-time guarantees about synchronization correctness.

Caldera fills this gap: full Vulkan expressiveness, zero runtime overhead, compile-time correctness guarantees.

---

## 5. Repository Structure

Caldera lives in the same workspace as CuTe-RS. The two projects share the Verus verification infrastructure and have a direct integration point at compute dispatch.

```
cute-rs/                                # Shared workspace root
├── Cargo.toml                          # Workspace members include caldera crates
│
├── crates/
│   ├── cute-rs-core/                   # (existing) Layout algebra + Verus specs
│   ├── cute-rs-macros/                 # (existing) Kernel proc macros
│   ├── cute-rs-runtime/               # (existing) Compute dispatch runtime
│   ├── cute-rs/                        # (existing) Compute facade crate
│   │
│   ├── caldera-core/                   # Vulkan ghost state model
│   │   ├── Cargo.toml
│   │   └── src/
│   │       ├── lib.rs
│   │       ├── instance/
│   │       │   ├── mod.rs
│   │       │   ├── instance.rs         # VkInstance wrapper + ghost state
│   │       │   ├── physical_device.rs  # VkPhysicalDevice + capability model
│   │       │   └── device.rs           # VkDevice + queue family model
│   │       ├── memory/
│   │       │   ├── mod.rs
│   │       │   ├── allocator.rs        # Memory allocation + ghost tracking
│   │       │   ├── buffer.rs           # VkBuffer + ghost size/usage/binding
│   │       │   └── image.rs            # VkImage + ghost format/extent/layouts
│   │       ├── pipeline/
│   │       │   ├── mod.rs
│   │       │   ├── shader_module.rs    # VkShaderModule + interface model
│   │       │   ├── pipeline_layout.rs  # VkPipelineLayout + descriptor model
│   │       │   ├── graphics.rs         # VkPipeline (graphics) + state model
│   │       │   ├── compute.rs          # VkPipeline (compute) + state model
│   │       │   ├── dynamic_rendering.rs # VkRenderingInfo ghost model (primary)
│   │       │   └── render_pass.rs      # VkRenderPass legacy model (multi-subpass)
│   │       ├── descriptor/
│   │       │   ├── mod.rs
│   │       │   ├── set_layout.rs       # VkDescriptorSetLayout + binding model
│   │       │   ├── pool.rs             # VkDescriptorPool + allocation tracking
│   │       │   └── set.rs             # VkDescriptorSet + bound resource model
│   │       ├── sync/
│   │       │   ├── mod.rs
│   │       │   ├── fence.rs            # VkFence + signaled state model
│   │       │   ├── semaphore.rs        # VkSemaphore + timeline model
│   │       │   ├── barrier.rs          # Pipeline barrier type definitions
│   │       │   └── sync_model.rs       # Core synchronization state machine
│   │       ├── command/
│   │       │   ├── mod.rs
│   │       │   ├── pool.rs             # VkCommandPool wrapper
│   │       │   ├── buffer.rs           # VkCommandBuffer builder + ghost state
│   │       │   ├── render_cmds.rs      # Draw commands + verified preconditions
│   │       │   ├── compute_cmds.rs     # Dispatch commands + verified preconditions
│   │       │   ├── transfer_cmds.rs    # Copy/blit commands + verified preconditions
│   │       │   ├── sync_cmds.rs        # Barrier commands + state transitions
│   │       │   └── dynamic_state.rs    # Viewport, scissor, etc.
│   │       ├── presentation/
│   │       │   ├── mod.rs
│   │       │   ├── surface.rs          # VkSurfaceKHR wrapper
│   │       │   ├── swapchain.rs        # VkSwapchainKHR + image state model
│   │       │   └── present.rs          # vkQueuePresentKHR + verified submission
│   │       ├── queue/
│   │       │   ├── mod.rs
│   │       │   ├── queue.rs            # VkQueue + submission model
│   │       │   └── submit.rs           # vkQueueSubmit2 + verified ordering
│   │       └── proof/
│   │           ├── mod.rs
│   │           ├── sync_proofs.rs      # Lemmas about synchronization model
│   │           ├── layout_proofs.rs    # Lemmas about image layout transitions
│   │           ├── lifetime_proofs.rs  # Lemmas about resource lifetimes
│   │           └── helpers.rs          # Arithmetic and set-theory utilities
│   │
│   ├── caldera-vr/                     # VR-specific extensions
│   │   ├── Cargo.toml
│   │   └── src/
│   │       ├── lib.rs
│   │       ├── stereo.rs              # Stereo rendering state model
│   │       ├── multiview.rs           # VK_KHR_multiview integration
│   │       ├── timing.rs             # Frame pacing + deadline model
│   │       ├── openxr.rs             # OpenXR session integration
│   │       └── reprojection.rs       # Async reprojection pass verification
│   │
│   ├── caldera-bridge/                 # CuTe-RS ↔ Caldera integration
│   │   ├── Cargo.toml
│   │   └── src/
│   │       ├── lib.rs
│   │       ├── compute_dispatch.rs    # Launch CuTe-RS kernels through Caldera
│   │       ├── buffer_sharing.rs      # Shared buffer ghost state threading
│   │       └── proof/
│   │           └── dispatch_proofs.rs # Verified buffer size + sync at boundary
│   │
│   └── caldera/                        # Facade crate (public API)
│       ├── Cargo.toml
│       └── src/
│           ├── lib.rs                  # Re-exports
│           └── prelude.rs
│
├── examples/
│   ├── caldera_triangle.rs            # Verified hello-triangle
│   ├── caldera_stereo_vr.rs           # Verified stereo VR frame
│   ├── caldera_compute_blit.rs        # Compute + graphics interop
│   └── caldera_cute_gemm_viz.rs       # CuTe-RS GEMM → render result
│
├── tests/
│   ├── caldera/
│   │   ├── sync_model_tests.rs        # Property tests for sync state machine
│   │   ├── layout_transition_tests.rs # Exhaustive layout transition tests
│   │   ├── command_recording_tests.rs # Command sequence validity tests
│   │   ├── snapshot/
│   │   │   └── expected_ghost_states/ # Snapshot tests for ghost state evolution
│   │   └── integration/
│   │       ├── render_triangle.rs     # End-to-end rendering test
│   │       └── compute_readback.rs    # End-to-end compute test
│   └── verification/
│       └── run_caldera_verus.sh       # Verify all Caldera proof modules
│
└── docs/
    ├── caldera-design.md              # This document
    ├── caldera-sync-model.md          # Synchronization model reference
    ├── caldera-validity-coverage.md   # Which VUIDs are encoded, tracker
    └── caldera-vr-patterns.md         # Verified VR rendering patterns
```

---

## 6. The Ghost State Model

### 6.1 Foundational Principle

Every Vulkan object in Caldera is a pair: a runtime handle (the actual `VkImage`, `VkBuffer`, etc., via `ash`) and a ghost-level model of that object's state as the Vulkan specification defines it. The ghost model costs nothing at runtime — Verus erases it entirely during compilation — but is fully visible to the verifier. The ghost model is the ground truth that preconditions and postconditions reference.

The core insight is that the Vulkan specification is, at its heart, a description of a state machine. Resources have states (image layouts, buffer memory bindings, fence signaled status). Commands are transitions on those states, with preconditions on the current state. Caldera makes this state machine explicit and machine-checkable.

### 6.2 Resource Ghost State

Each resource type carries ghost fields that model the resource's properties and mutable state. Properties are set at creation time and never change. Mutable state evolves as commands reference the resource.

An `Image` carries ghost properties including its format, extent, mip level count, array layer count, sample count, tiling mode, usage flags, and sharing mode. It carries ghost mutable state including a map from subresource ranges to current image layouts and a synchronization tag (discussed in section 7). The creation function's `ensures` clause establishes the initial ghost state:

```rust
pub fn create_image(device: &Device, info: &ImageCreateInfo) -> Result<Image>
    ensures
        match result {
            Ok(image) => {
                image.ghost_format == info.format
                && image.ghost_extent == info.extent
                && image.ghost_mip_levels == info.mip_levels as nat
                && image.ghost_usage == info.usage
                && forall |sr| image.ghost_layout(sr) == vk::ImageLayout::UNDEFINED
                && image.ghost_sync == SyncState::initial()
            }
            Err(_) => true  //  Creation can fail; no ghost state to establish
        }
{
    ...
}
```

A `Buffer` carries ghost properties including its size, usage flags, and sharing mode, and ghost mutable state including its memory binding (which device memory, at what offset) and synchronization tag. The memory binding ghost state is set by `bind_buffer_memory` and is a precondition for any command that accesses the buffer:

```rust
pub fn cmd_copy_buffer(
    &mut self,
    src: &Buffer,
    dst: &Buffer,
    regions: &[BufferCopy],
)
    requires
        self.is_recording(),
        !self.inside_render_pass(),
        src.ghost_is_bound(),       //  Memory must be bound
        dst.ghost_is_bound(),
        src.ghost_usage.contains(TRANSFER_SRC),
        dst.ghost_usage.contains(TRANSFER_DST),
        //  All copy regions must be in bounds
        forall |r: &BufferCopy| regions.contains(r) ==> {
            r.src_offset + r.size <= src.ghost_size
            && r.dst_offset + r.size <= dst.ghost_size
        },
        //  No overlapping regions when src == dst
        src.ghost_handle != dst.ghost_handle
            || no_overlap(regions),
        //  Synchronization: src readable, dst writable at TRANSFER stage
        self.ghost_sync.readable(src, PipelineStage::TRANSFER),
        self.ghost_sync.writable(dst, PipelineStage::TRANSFER),
{
    ...
}
```

A `DescriptorSet` carries a ghost model of what resources are currently bound to each binding slot. When you call `update_descriptor_sets`, the ghost model is updated. When you call `cmd_bind_descriptor_sets`, the command buffer builder's ghost state records the bound set. When you call `cmd_draw`, the precondition checks that the bound descriptor set's ghost bindings are compatible with the pipeline layout's expected bindings and that all referenced resources are in the correct state.

### 6.3 Command Buffer Ghost State

The command buffer builder is the most state-heavy object in the system. Its ghost state models the "recording cursor" — the abstract Vulkan state at the current point in the command sequence. This includes whether the command buffer is in the initial, recording, or executable state; whether a render pass instance is active and if so which subpass; which graphics pipeline is bound; which compute pipeline is bound; which descriptor sets are bound to each bind point; which vertex and index buffers are bound; the current dynamic state (viewport, scissor, blend constants, depth bounds, stencil reference); and the synchronization model's state (which resources have been barriered and how).

Each command recording function takes `&mut self`, reads the ghost state in its `requires` clause, and updates the ghost state in its `ensures` clause:

```rust
pub fn cmd_begin_render_pass(
    &mut self,
    info: &RenderPassBeginInfo,
    contents: SubpassContents,
)
    requires
        self.is_recording(),
        !self.inside_render_pass(),   //  Can't nest render passes
        info.render_pass.ghost_subpass_count > 0,
        info.framebuffer.ghost_compatible_with(info.render_pass),
        //  All attachments in correct layout
        forall |i: nat| i < info.framebuffer.ghost_attachment_count() ==> {
            let img = info.framebuffer.ghost_attachment_image(i);
            let expected = info.render_pass.ghost_initial_layout(i);
            self.ghost_image_layout(img) == expected
                || expected == vk::ImageLayout::UNDEFINED
        },
    ensures
        self.inside_render_pass(),
        self.ghost_current_render_pass() == info.render_pass,
        self.ghost_current_subpass() == 0,
        self.ghost_subpass_contents() == contents,
        //  Attachment layouts transition to first subpass layouts
        forall |i: nat| i < info.framebuffer.ghost_attachment_count() ==> {
            let layout = info.render_pass.ghost_subpass_layout(0, i);
            self.ghost_image_layout(info.framebuffer.ghost_attachment_image(i))
                == layout
        },
{
    ...
}
```

The `ensures` clause on `cmd_begin_render_pass` updates the ghost state to reflect that a render pass is now active, the current subpass is 0, and the attachment image layouts have transitioned to the layouts declared in the first subpass description. This ghost state then flows into subsequent draw commands and `cmd_next_subpass`/`cmd_end_render_pass` calls.

### 6.4 The Ghost State Threading Model

A critical design question is how ghost state flows through the program. Vulkan objects are shared — multiple command buffers can reference the same image. But the ghost state of an image (its current layout) changes as commands reference it. How do we prevent inconsistency?

The answer is that ghost state for mutable resource properties (image layouts, synchronization status) is owned by the entity that controls the mutation. During command buffer recording, the command buffer builder owns a ghost copy of every resource's state as it will be at that point in execution. This ghost copy starts from the resource's "known" state at the time recording begins and evolves as barrier and render pass commands are recorded.

At queue submission time, the ghost state model verifies that the submitted command buffers' assumptions about initial resource states match reality. The submission function's `ensures` clause then updates the "known" state of each affected resource to reflect the final state after the command buffer executes. The fence or semaphore associated with the submission carries ghost state indicating what resource states are established when it signals.

This is conceptually similar to Rust's ownership model — the command buffer builder "borrows" the ghost state of resources during recording and "returns" it at submission — but it operates entirely at the ghost level and doesn't restrict the runtime API usage.

### 6.5 Resource Destruction and Lifetime Tracking

Every Vulkan resource has a lifecycle: create, use, destroy. The Vulkan specification requires that a resource must not be destroyed while any command buffer referencing it is pending execution, and must not be used after destruction. Violating either rule is undefined behavior — use-after-free on the GPU.

Caldera tracks liveness with a ghost boolean on each resource:

```rust
pub struct Buffer {
    handle: vk::Buffer,
    ghost alive: bool,
    ghost properties: BufferProperties,
    ghost sync: SyncState,
}
```

Creation sets `alive = true`. Every `cmd_*` function that references a resource requires `resource.ghost_alive`. Destruction sets `alive = false` and requires that no pending submissions reference the resource:

```rust
pub fn destroy_buffer(device: &Device, buffer: &mut Buffer)
    requires
        buffer.ghost_alive,
        //  No command buffer in the pending state references this buffer.
        //  This is tracked through the device's ghost submission log.
        device.ghost_no_pending_references(buffer.ghost_handle),
    ensures
        !buffer.ghost_alive,
{
    ...
}
```

The `ghost_no_pending_references` predicate queries the device's ghost submission log — a ghost sequence of `(command_buffer_id, resource_set, fence_or_semaphore)` entries. When a fence is waited on (or `vkDeviceWaitIdle` is called), the corresponding entries are removed from the ghost log. A resource has no pending references when no entry in the log contains it.

```rust
pub open spec fn ghost_no_pending_references(
    &self,
    handle: vk::Buffer,
) -> bool {
    forall |i: nat| i < self.ghost_pending_submissions.len() ==> {
        !self.ghost_pending_submissions[i].references.contains(handle)
    }
}
```

`vkWaitForFences` and `vkDeviceWaitIdle` update the ghost submission log:

```rust
pub fn wait_for_fences(device: &mut Device, fences: &[&Fence], wait_all: bool)
    requires
        wait_all,  //  v0.1: only support wait_all=true
        forall |f| fences.contains(f) ==> f.ghost_is_signaled() || f.ghost_is_pending(),
    ensures
        //  All fences are now signaled
        forall |f| fences.contains(f) ==> f.ghost_is_signaled(),
        //  Submissions guarded by these fences are removed from pending log
        forall |i: nat| i < old(device).ghost_pending_submissions.len() ==> {
            let sub = old(device).ghost_pending_submissions[i];
            fences.contains(&sub.fence) ==>
                !device.ghost_pending_submissions.contains(sub)
        },
{
    ...
}
```

This creates a clean verification flow: you submit work with a fence, wait on the fence (which clears the ghost pending log), and then you can destroy resources. If you try to destroy a resource before waiting on the fence, the `ghost_no_pending_references` precondition fails and Verus rejects the program.

The ghost submission log grows with each `queue_submit` and shrinks with each `wait_for_fences`/`device_wait_idle`. In a typical frame loop this stays bounded — you submit frame N's work, wait on frame N-2's fence, destroy frame N-2's transient resources. The ghost log at any point contains at most the in-flight frame count worth of entries.

**Leak prevention.** Beyond use-after-free, Caldera also verifies that resources are not leaked. The `Device` tracks a ghost resource count:

```rust
pub struct Device {
    handle: vk::Device,
    ghost live_buffers: nat,
    ghost live_images: nat,
    ghost live_descriptor_pools: nat,
    ghost live_pipelines: nat,
    //  ... one counter per resource type
}
```

Every `create_*` increments the corresponding counter; every `destroy_*` decrements it. The `device_shutdown` function (which wraps `vkDestroyDevice`) requires all counters are zero:

```rust
pub fn device_shutdown(device: Device)
    requires
        device.ghost_pending_submissions.len() == 0,  //  All work completed
        device.ghost_live_buffers == 0,
        device.ghost_live_images == 0,
        device.ghost_live_descriptor_pools == 0,
        device.ghost_live_pipelines == 0,
        //  ... all resource types
{
    ...
}
```

If you forget to destroy a buffer, Verus rejects the program at the `device_shutdown` call. For long-running VR applications, this is critical — a slow leak of one buffer per frame will OOM the GPU after a few hours. By requiring a clean zero at shutdown, Caldera forces the programmer to account for every resource.

For applications that create resources dynamically (e.g., streaming assets), the frame loop's invariant would include a bound on resource counts:

```rust
while running
    invariant
        device.ghost_live_buffers <= MAX_STREAMING_BUFFERS,
        device.ghost_live_images <= MAX_STREAMING_IMAGES,
{
    //  ... frame logic that creates and destroys transient resources
}
```

This is ghost integer arithmetic — the simplest pattern Verus handles, but it catches a class of bugs that has historically been very difficult to find with runtime tools because the symptom (GPU OOM) manifests hours after the cause (one leaked allocation per frame).

### 6.6 Ghost Checkpoints for Long Command Sequences

Recording a command buffer can involve dozens or hundreds of `cmd_*` calls. Each call's `ensures` clause establishes ghost state that the next call's `requires` clause consumes. Naively, this creates a chain of 50+ nested postcondition references that Z3 must reason through. Experience from verus-topology's construction proofs (Phase B alone has ~20 loop iterations with 15+ ghost fields each) shows that Z3 struggles with long chains — rlimit explodes and verification times become unpredictable.

Caldera addresses this with **ghost checkpoints**: explicit points in a command sequence where the accumulated ghost state is snapshot and future verification only needs to reference the checkpoint, not the full history before it.

```rust
pub fn ghost_checkpoint(&mut self) -> (checkpoint: Ghost<CommandBufferSnapshot>)
    ensures
        checkpoint@ == self.ghost_snapshot(),
        //  The checkpoint captures ALL current ghost state
        checkpoint@.sync_state == self.ghost_sync_state(),
        checkpoint@.bound_pipeline == self.ghost_bound_pipeline(),
        checkpoint@.render_pass_state == self.ghost_render_pass_state(),
        checkpoint@.image_layouts == self.ghost_image_layouts(),
{
    //  No-op at runtime — purely ghost
    Ghost(self.ghost_snapshot())
}
```

The intended usage pattern mirrors verus-topology's phase snapshots:

```rust
//  Phase 1: Upload
cmd.cmd_copy_buffer(&staging, &vertex_buf, &[region]);
cmd.cmd_copy_buffer(&staging, &index_buf, &[region]);
let post_upload = cmd.ghost_checkpoint();

//  Phase 2: Barriers (verifier only needs post_upload, not upload details)
cmd.cmd_pipeline_barrier(&upload_to_compute_barrier);
let post_barrier = cmd.ghost_checkpoint();

//  Phase 3: Compute (verifier only needs post_barrier)
cmd.cmd_bind_pipeline(PipelineBindPoint::COMPUTE, &skin_pipeline);
cmd.cmd_dispatch(groups, 1, 1);
let post_compute = cmd.ghost_checkpoint();

//  Phase 4: Render (verifier only needs post_compute)
cmd.cmd_pipeline_barrier(&compute_to_graphics_barrier);
cmd.cmd_begin_render_pass(&rp_info, SubpassContents::INLINE);
//  ...draw commands...
cmd.cmd_end_render_pass();
```

Each phase verifies against the previous checkpoint's ghost state, not the full command history. This is the same "frame invariant" pattern that made verus-topology's construction proofs tractable: Phase C's loop verified against `post_phase_b`, Phase D verified against `post_phase_c`, etc.

For loops that record many similar commands (e.g., drawing 100 meshes), the loop invariant carries the ghost checkpoint forward:

```rust
let mut checkpoint = cmd.ghost_checkpoint();
let mut i: usize = 0;
while i < mesh_count
    invariant
        cmd.ghost_snapshot() == checkpoint@
            .with_draws(i as nat),  //  Abstract: "i draws have been recorded"
        //  Sync state: all previously-drawn meshes' resources are still valid
        forall |j: nat| j < i as nat ==>
            cmd.ghost_sync.readable(meshes[j].vertex_buffer, VERTEX_INPUT),
{
    cmd.cmd_bind_vertex_buffers(0, &[&meshes[i].vertex_buffer], &[0]);
    cmd.cmd_draw(meshes[i].vertex_count, 1, 0, 0);
    i += 1;
}
```

### 6.7 GPU Memory Budget Verification

Vulkan applications manage GPU memory explicitly via `vkAllocateMemory` and `vkFreeMemory`. Each physical device has a fixed number of memory heaps with fixed sizes. Exceeding a heap's capacity causes allocation failure, which in many applications is fatal. Unlike CPU memory, there is no swap — when GPU memory is full, it's full.

Caldera tracks memory consumption per heap as ghost state on the `Device`:

```rust
pub struct Device {
    //  ...
    ghost heap_usage: Map<u32, nat>,    //  heap_index → bytes currently allocated
    ghost heap_capacity: Map<u32, nat>, //  heap_index → max bytes (from physical device)
}
```

`allocate_memory` updates the ghost usage and requires the allocation fits:

```rust
pub fn allocate_memory(
    device: &mut Device,
    info: &MemoryAllocateInfo,
) -> Result<DeviceMemory>
    requires
        info.memory_type_index < device.ghost_memory_type_count(),
        //  The allocation must fit within the heap's remaining capacity
        device.ghost_heap_usage[device.ghost_heap_for_type(info.memory_type_index)]
            + info.allocation_size as nat
            <= device.ghost_heap_capacity[device.ghost_heap_for_type(info.memory_type_index)],
    ensures
        match result {
            Ok(mem) => {
                mem.ghost_size == info.allocation_size as nat
                && mem.ghost_heap == device.ghost_heap_for_type(info.memory_type_index)
                //  Heap usage updated
                && device.ghost_heap_usage[mem.ghost_heap]
                    == old(device).ghost_heap_usage[mem.ghost_heap] + info.allocation_size as nat
            }
            Err(_) => true
        }
{
    ...
}
```

`free_memory` decrements the usage. The invariant `forall |h| heap_usage[h] <= heap_capacity[h]` is maintained across the application's lifetime.

This is conservative — it prevents the application from ever attempting an allocation that would exceed device limits. For VR, where allocation failure mid-frame would be catastrophic (device loss or black screen), this is exactly the right trade-off. The ghost tracking is just integer arithmetic with a running sum, which Verus handles trivially.

In practice, most VR applications pre-allocate all GPU memory at startup and suballocate from pools. Caldera's memory budget verification composes cleanly with this pattern: the startup function's `ensures` clause establishes the total allocation, and the frame loop's invariant proves that suballocation stays within the pre-allocated pool without additional `vkAllocateMemory` calls.

---

## 7. The Synchronization Model

### 7.1 Why This Is the Hardest Part

GPU synchronization is the primary source of Vulkan bugs in production applications. The mental model is deceptively simple — "put a barrier between the write and the read" — but the details are treacherous. Pipeline barriers operate on pipeline stages and access types, not on individual commands. Memory barriers and execution barriers are separate concepts that must both be correct. Image layout transitions are synchronization operations with side effects. Cross-queue synchronization requires explicit ownership transfers. And the whole system operates on a partial order, not a total order — commands within a render pass subpass can execute in any order unless you add dependencies.

A synchronization bug typically manifests as a data race on the GPU: one command reads a resource while another command is still writing it. The symptoms are nondeterministic — the program works 99.9% of the time because the GPU happens to schedule things in a safe order, and then one frame in a thousand it produces garbage. These bugs are nearly impossible to reproduce, nearly impossible to diagnose with traditional debugging tools, and nearly impossible to test for. They are the single strongest argument for formal verification of Vulkan usage.

### 7.2 The Abstract Synchronization State Machine

Caldera models synchronization using an abstract state machine inspired by the Vulkan specification's "synchronization scopes" formalism but simplified for practical verification.

Each resource (buffer or image subresource) carries a ghost `SyncState`:

```rust
pub ghost struct SyncState {
    pub last_write: Option<SyncPoint>,
    pub last_reads: Set<SyncPoint>,
}

pub ghost struct SyncPoint {
    pub stage: vk::PipelineStageFlags2,
    pub access: vk::AccessFlags2,
    pub queue_family: u32,
    pub submission_order: nat,    //  Monotonic counter per queue
    pub barrier_epoch: nat,       //  Incremented by each barrier
}
```

A `SyncPoint` represents a point in the execution timeline where a resource was accessed. The `barrier_epoch` field is the key mechanism: each pipeline barrier that includes a resource in its dependency chain increments the epoch for that resource's sync state. A subsequent access is safe if it can "see" the previous access's epoch through a chain of barriers.

The core safety invariant is: a read is safe if there exists a barrier chain from the last write to the current read. A write is safe if there exists a barrier chain from all previous accesses (both reads and writes) to the current write. "Barrier chain" means a sequence of pipeline barriers where each barrier's destination stage mask includes the source stage mask of the next access.

In Verus, this becomes:

```rust
pub open spec fn readable(
    &self,
    resource: &impl Resource,
    reading_stage: vk::PipelineStageFlags2,
) -> bool {
    match resource.ghost_sync().last_write {
        None => true,  //  Never written — always safe to read
        Some(write_point) => {
            //  There must be a barrier whose src includes the write's stage/access
            //  and whose dst includes the reading stage
            self.barrier_chain_exists(write_point, reading_stage)
        }
    }
}

pub open spec fn writable(
    &self,
    resource: &impl Resource,
    writing_stage: vk::PipelineStageFlags2,
) -> bool {
    //  Must be barriered from the last write (WAW hazard)
    self.readable(resource, writing_stage)
    //  AND must be barriered from all outstanding reads (WAR hazard)
    && forall |read_point| resource.ghost_sync().last_reads.contains(read_point) ==> {
        self.barrier_chain_exists(read_point, writing_stage)
    }
}
```

### 7.3 Formalizing Barrier Chains

The `barrier_chain_exists` predicate is the core of the synchronization model and the hardest piece to formalize correctly. The Vulkan specification defines synchronization in terms of "synchronization scopes" and "execution/memory dependency chains." Caldera simplifies this into a concrete ghost data structure that Verus can reason about efficiently.

The key insight is that within a single command buffer on a single queue, barrier chains are linear — each barrier fully orders everything before it with everything after it (for the stages in its scope). We don't need to model arbitrary DAGs. The ghost state tracks a **barrier log**: a ghost sequence of barrier records, ordered by recording position.

```rust
pub ghost struct BarrierLog {
    pub entries: Seq<BarrierEntry>,
}

pub ghost struct BarrierEntry {
    pub position: nat,          //  Recording order index
    pub src_stage: PipelineStageFlags2,
    pub src_access: AccessFlags2,
    pub dst_stage: PipelineStageFlags2,
    pub dst_access: AccessFlags2,
    pub resource: ResourceId,   //  Which resource (or ALL for global memory barriers)
}
```

A barrier chain exists from a write point to a read stage if there is a barrier entry in the log that:
1. Was recorded after the write (position > write_point.position)
2. Has `src_stage` that includes the write's stage
3. Has `src_access` that includes the write's access type (memory dependency)
4. Has `dst_stage` that includes the reading stage
5. Covers the resource in question

```rust
pub open spec fn barrier_chain_exists(
    &self,
    from: SyncPoint,
    to_stage: PipelineStageFlags2,
    resource: ResourceId,
) -> bool {
    exists |i: nat| i < self.barrier_log.entries.len() && {
        let entry = self.barrier_log.entries[i];
        //  Barrier was recorded after the source access
        entry.position > from.position
        //  Execution dependency: src scope includes the write's stage
        && entry.src_stage.contains(from.stage)
        //  Memory dependency: src access includes the write's access
        && entry.src_access.contains(from.access)
        //  Execution dependency: dst scope includes the read's stage
        && entry.dst_stage.contains(to_stage)
        //  Covers this resource (or is a global memory barrier)
        && (entry.resource == resource || entry.resource == ResourceId::All)
    }
}
```

This formulation is deliberately simpler than the full Vulkan spec, which allows multi-hop barrier chains (A→B→C where barrier 1 covers A→B and barrier 2 covers B→C). In practice, multi-hop chains are rare and fragile — most real code uses a single barrier that covers the full src→dst transition. Caldera v0.1 requires direct barrier coverage. Multi-hop chains can be added later by extending `barrier_chain_exists` to a transitive closure, but this adds proof complexity (induction over chain length) that isn't worth the cost initially.

**Why existential quantifiers are tractable here:** The `exists |i|` in `barrier_chain_exists` might seem expensive for Z3, but the barrier log is short (typically 5–20 entries per command buffer) and each `cmd_pipeline_barrier` call provides a concrete witness — its `ensures` clause asserts that a new entry exists at position `self.barrier_log.entries.len() - 1`. Subsequent `readable`/`writable` checks can use this witness directly via `assert(self.barrier_chain_exists(...)) by { ... }` blocks that instantiate the existential with the known barrier index. This is the same pattern used in verus-topology's `face_representative_cycles` proof, where existential witnesses are provided explicitly rather than leaving Z3 to search.

**Render pass implicit barriers:** Render passes create implicit synchronization between subpasses (and between the render pass and external commands) via subpass dependencies. These are modeled by injecting synthetic barrier entries into the log when `cmd_begin_render_pass`, `cmd_next_subpass`, and `cmd_end_render_pass` are recorded:

```rust
//  In cmd_begin_render_pass ensures:
//  For each external→subpass0 dependency in the render pass:
forall |dep: &DependencyModel|
    info.render_pass.ghost_dependencies().contains(dep)
    && dep.src_subpass == vk::SUBPASS_EXTERNAL
    && dep.dst_subpass == 0 ==> {
        //  A synthetic barrier entry is added to the log
        self.barrier_log.entries.last() == BarrierEntry {
            src_stage: dep.src_stage_mask,
            src_access: dep.src_access_mask,
            dst_stage: dep.dst_stage_mask,
            dst_access: dep.dst_access_mask,
            resource: ResourceId::All,  //  Subpass deps are global
            ..
        }
    }
```

### 7.4 Pipeline Barrier Ghost Updates

When `cmd_pipeline_barrier` is recorded, it updates the command buffer builder's ghost synchronization state:

```rust
pub fn cmd_pipeline_barrier(
    &mut self,
    dependency_info: &DependencyInfo,
)
    requires
        self.is_recording(),
    ensures
        //  For each memory barrier: all resources' sync states are advanced
        //  For each buffer memory barrier: named buffer's sync state is advanced
        //  For each image memory barrier: named image subresource's sync state
        //    is advanced AND its layout ghost state transitions
        forall |imb: &ImageMemoryBarrier2|
            dependency_info.image_memory_barriers.contains(imb) ==> {
                //  Layout transition
                self.ghost_image_layout(imb.image, imb.subresource_range)
                    == imb.new_layout
                //  Sync advancement
                && self.ghost_sync_epoch(imb.image, imb.subresource_range)
                    == old(self).ghost_sync_epoch(imb.image, imb.subresource_range) + 1
                //  The barrier records its src/dst stage+access for chain validation
                && self.ghost_last_barrier(imb.image, imb.subresource_range)
                    == BarrierRecord {
                        src_stage: imb.src_stage_mask,
                        src_access: imb.src_access_mask,
                        dst_stage: imb.dst_stage_mask,
                        dst_access: imb.dst_access_mask,
                    }
            },
{
    ...
}
```

The image memory barrier case is particularly important because it's where layout transitions happen. The `ensures` clause guarantees that after the barrier, the ghost image layout matches `new_layout`. This is what makes the `cmd_begin_render_pass` precondition (which checks that attachment layouts match the render pass's initial layouts) verifiable — you must have recorded a barrier transitioning the image to the correct layout before beginning the render pass, and Verus tracks this through the ghost state.

### 7.5 Semaphore-Based Cross-Submission Synchronization

When work is submitted to a queue with `vkQueueSubmit2`, the submission can signal semaphores and wait on semaphores. Semaphores carry ghost state representing what resource states are guaranteed when the semaphore is signaled.

```rust
pub fn queue_submit(
    &mut self,
    queue: &Queue,
    submits: &[SubmitInfo2],
    fence: Option<&Fence>,
)
    requires
        //  Each wait semaphore must have been signaled
        forall |s| submits.wait_semaphores().contains(s) ==>
            s.semaphore.ghost_is_signaled(),
        //  Each command buffer's initial ghost state must match
        //  the current known state of its referenced resources
        //  (after accounting for waited semaphores' guarantees)
        ...
    ensures
        //  Signal semaphores carry the post-execution ghost state
        forall |s| submits.signal_semaphores().contains(s) ==>
            s.semaphore.ghost_is_signaled()
            && s.semaphore.ghost_resource_states() ==
                post_execution_states(submits),
        //  Fence (if any) carries the same guarantee
        fence.is_some() ==>
            fence.unwrap().ghost_is_signaled()
            && ...,
{
    ...
}
```

When a subsequent submission waits on that semaphore, the waited semaphore's ghost resource states become the "known" initial states for that submission's command buffers. This is how Verus verifies cross-submission synchronization: the ghost state flows through semaphores.

### 7.6 Swapchain Protocol Verification

The swapchain acquire→render→present cycle is a state machine, and violating it causes deadlocks or undefined behavior. Vulkan allows at most N images in flight (where N is the swapchain image count). If you acquire N+1 images without presenting any, `vkAcquireNextImageKHR` blocks forever. If you present an image you never rendered to, the user sees garbage. If you acquire an image and never present it, the swapchain leaks a slot.

Caldera models this with a ghost enum per swapchain image slot:

```rust
pub ghost enum SwapchainImageState {
    Available,                  //  Owned by presentation engine
    Acquired { frame_id: nat }, //  Application has it, not yet rendered
    Rendered { frame_id: nat }, //  Render commands recorded and submitted
    Presented,                  //  Queued for presentation, will become Available
}
```

`acquire_next_image` requires that the number of currently acquired/rendered images is less than `swapchain.ghost_image_count() - 1` (the Vulkan spec's in-flight limit) and transitions the acquired image from `Available` to `Acquired`:

```rust
pub fn acquire_next_image(
    device: &Device,
    swapchain: &mut Swapchain,
    semaphore: &Semaphore,
) -> Result<u32>
    requires
        //  Must not exceed in-flight limit
        swapchain.ghost_in_flight_count() < swapchain.ghost_image_count() - 1,
    ensures
        match result {
            Ok(index) => {
                index < swapchain.ghost_image_count() as u32
                && old(swapchain).ghost_image_state(index as nat) == SwapchainImageState::Available
                && swapchain.ghost_image_state(index as nat)
                    == SwapchainImageState::Acquired { frame_id: swapchain.ghost_frame_counter() }
                && semaphore.ghost_is_signaled()
                //  All other slots unchanged
                && forall |i: nat| i < swapchain.ghost_image_count() && i != index as nat ==>
                    swapchain.ghost_image_state(i) == old(swapchain).ghost_image_state(i)
            }
            Err(_) => true
        }
{
    ...
}
```

`queue_present` requires the image is in `Rendered` state (you must have submitted render commands) and transitions it to `Presented`:

```rust
pub fn queue_present(
    queue: &Queue,
    swapchain: &mut Swapchain,
    image_index: u32,
    wait_semaphore: &Semaphore,
)
    requires
        wait_semaphore.ghost_is_signaled(),
        image_index < swapchain.ghost_image_count() as u32,
        //  Can't present an image you haven't rendered to
        swapchain.ghost_image_state(image_index as nat).is_rendered(),
    ensures
        swapchain.ghost_image_state(image_index as nat) == SwapchainImageState::Presented,
{
    ...
}
```

The `Acquired` → `Rendered` transition happens at `queue_submit` time, when the command buffer that draws to the swapchain image is submitted. The `Presented` → `Available` transition is handled by the presentation engine (modeled as happening atomically at `acquire_next_image` time for the returned index).

This ghost state machine catches three real bug classes:
1. **Acquire without present (deadlock):** The `ghost_in_flight_count()` precondition prevents acquiring more images than the swapchain can handle.
2. **Present without render (garbage frame):** The `is_rendered()` precondition on `queue_present` prevents presenting an image that was never drawn to.
3. **Double acquire (protocol violation):** An `Available` state precondition on the acquired index prevents acquiring an image that's already in flight.

### 7.7 What the Sync Model Does Not Cover

The synchronization model as described handles intra-queue synchronization (barriers), inter-submission synchronization (semaphores and fences), image layout transitions, and swapchain protocol correctness. It does not model subpass self-dependencies (an advanced feature rarely needed), fine-grained execution ordering within a subpass (commands within a subpass are unordered by default, which is safe for Caldera's purposes because we only require that barriers are present, not that commands execute in a particular order), or host-side synchronization (mapping memory, host reads of GPU-written data). Host-side synchronization involves `vkWaitForFences` and `vkDeviceWaitIdle`, which will be modeled in a later iteration.

---

## 8. The Validity Rule Encoding

### 8.1 Strategy

The Vulkan specification assigns each validity rule a unique identifier (VUID). There are over 3,000 VUIDs in Vulkan 1.3. Encoding all of them is unrealistic for v0.1 and probably unnecessary — many apply to obscure features. Caldera's strategy is to prioritize VUIDs by two criteria: frequency (how often the rule is relevant in typical rendering code) and severity (how bad the consequences are when the rule is violated).

The highest-priority categories are synchronization rules (GPU data races cause nondeterministic corruption), image layout rules (wrong layout causes garbled textures or driver crashes), render pass compatibility rules (incompatible framebuffer/render pass causes device loss), descriptor set validity rules (wrong descriptor causes reads from freed memory), and buffer/image bounds rules (out-of-bounds access causes device loss or security vulnerabilities).

Lower-priority categories deferred to later versions include format feature checking (whether a format supports a given usage on the current device), pipeline derivative rules, query pool rules, sparse resource rules, and multi-queue ownership transfer rules (single-queue first, multi-queue later).

### 8.2 Coverage Tracking

The `docs/caldera-validity-coverage.md` file maintains a table mapping VUIDs to their Caldera status: verified (encoded as a Verus precondition), runtime-checked (checked by an assert at runtime, not formally verified), trusted (assumed correct, not checked), or not-applicable (feature not supported). This table is the project's honest accounting of its verification coverage and is updated with every PR.

### 8.3 Encoding Patterns

Most VUIDs fall into a few patterns that map to natural Verus constructs.

Flag requirements ("usage must include X") become simple ghost field checks in `requires` clauses. These are trivial to verify — Verus solves them instantly.

State requirements ("must be in recording state," "must not be inside a render pass") become checks on the command buffer builder's ghost state enum. Also trivial.

Compatibility requirements ("framebuffer must be compatible with render pass") become spec functions that compare the ghost models of two objects. These are more complex but still straightforward — they're comparing tree-structured data.

Size/bounds requirements ("offset + size must not exceed buffer size") become integer arithmetic preconditions. These are the bread and butter of Verus.

Synchronization requirements ("there must be an execution dependency between X and Y") become the sync model queries described in section 7. These are the most complex and require the most proof engineering.

### 8.4 Shader-Pipeline Interface Verification

A common Vulkan bug is updating a shader but forgetting to update the pipeline layout, vertex input state, or descriptor set layout to match. The result is silent misinterpretation of data — the vertex shader reads position data as normals, or the fragment shader samples from the wrong binding. The validation layers catch some of these at runtime, but not all (especially for push constants and vertex attribute format mismatches).

Caldera models the shader's interface as ghost state on `ShaderModule`:

```rust
pub ghost struct ShaderInterface {
    pub stage: vk::ShaderStageFlags,
    pub inputs: Seq<ShaderInputAttribute>,   //  Vertex shader inputs
    pub outputs: Seq<ShaderOutputAttribute>,  //  Fragment shader outputs
    pub descriptor_bindings: Seq<ShaderDescriptorBinding>,
    pub push_constant_range: Option<PushConstantRange>,
}

pub ghost struct ShaderInputAttribute {
    pub location: nat,
    pub format: vk::Format,    //  Expected format (e.g., R32G32B32_SFLOAT)
    pub name: Seq<char>,       //  For diagnostics only
}

pub ghost struct ShaderDescriptorBinding {
    pub set: nat,
    pub binding: nat,
    pub descriptor_type: vk::DescriptorType,
    pub count: nat,
    pub stage_flags: vk::ShaderStageFlags,
}
```

The `ShaderInterface` is established at `create_shader_module` time. In practice, it's extracted from SPIR-V reflection data (via `spirv-reflect` or similar) and embedded as ghost state. The `create_graphics_pipeline` function then verifies compatibility:

```rust
pub fn create_graphics_pipeline(
    device: &Device,
    info: &GraphicsPipelineCreateInfo,
) -> Result<Pipeline>
    requires
        //  Vertex input state matches vertex shader's expected inputs
        forall |i: nat| i < info.vertex_shader.ghost_interface().inputs.len() ==> {
            let attr = info.vertex_shader.ghost_interface().inputs[i];
            //  There must be a vertex input attribute at this location with matching format
            exists |j: nat| j < info.vertex_input_state.attributes.len() && {
                let vk_attr = info.vertex_input_state.attributes[j];
                vk_attr.location == attr.location as u32
                && format_compatible(vk_attr.format, attr.format)
            }
        },
        //  Descriptor set layouts match shader's expected bindings
        forall |binding: &ShaderDescriptorBinding|
            info.vertex_shader.ghost_interface().descriptor_bindings.contains(binding)
            || info.fragment_shader.ghost_interface().descriptor_bindings.contains(binding) ==> {
                binding.set < info.layout.ghost_set_layouts().len()
                && info.layout.ghost_set_layouts()[binding.set]
                    .ghost_has_binding(binding.binding, binding.descriptor_type, binding.count)
            },
        //  Fragment shader output count matches color attachment count
        info.fragment_shader.ghost_interface().outputs.len()
            == info.color_blend_state.attachment_count as nat,
        //  Push constant ranges cover shader requirements
        info.vertex_shader.ghost_interface().push_constant_range.is_some() ==> {
            info.layout.ghost_push_constant_ranges_cover(
                info.vertex_shader.ghost_interface().push_constant_range.unwrap()
            )
        },
{
    ...
}
```

This catches the entire "shader/pipeline mismatch" class of bugs at verification time. The programmer changes a shader, Verus tells them which pipeline create calls now have unsatisfied preconditions.

### 8.5 Descriptor Set Coherence

The current ghost model (section 6.2) tracks what resources are bound to each descriptor set slot. Section 8.4 verifies that the pipeline layout matches the shader. Descriptor set coherence completes the chain: at draw time, the bound descriptor set's contents must satisfy the shader's expectations.

```rust
pub fn cmd_draw(
    &mut self,
    vertex_count: u32,
    instance_count: u32,
    first_vertex: u32,
    first_instance: u32,
)
    requires
        self.is_recording(),
        self.inside_render_pass(),
        self.ghost_bound_graphics_pipeline().is_some(),
        //  Descriptor set coherence: every binding expected by the shader
        //  has a valid resource bound with correct type and sufficient size
        forall |binding: &ShaderDescriptorBinding|
            self.ghost_bound_pipeline_shader_bindings().contains(binding) ==> {
                let desc_set = self.ghost_bound_descriptor_set(binding.set);
                desc_set.is_some()
                && desc_set.unwrap().ghost_binding_type(binding.binding)
                    == binding.descriptor_type
                && desc_set.unwrap().ghost_binding_count(binding.binding)
                    >= binding.count
                //  Bound resources are alive and in correct state
                && desc_set.unwrap().ghost_binding_resources_alive(binding.binding)
                && match binding.descriptor_type {
                    UNIFORM_BUFFER | STORAGE_BUFFER => {
                        //  Buffer is bound, has sufficient size, correct usage flags
                        desc_set.unwrap().ghost_binding_buffer_size(binding.binding)
                            >= binding.min_size
                    }
                    COMBINED_IMAGE_SAMPLER => {
                        //  Image view format matches shader expectation
                        //  Image is in SHADER_READ_ONLY_OPTIMAL layout
                        desc_set.unwrap().ghost_binding_image_layout(binding.binding)
                            == vk::ImageLayout::SHADER_READ_ONLY_OPTIMAL
                    }
                    STORAGE_IMAGE => {
                        desc_set.unwrap().ghost_binding_image_layout(binding.binding)
                            == vk::ImageLayout::GENERAL
                    }
                    _ => true
                }
            },
        //  Vertex buffer bound with sufficient size
        self.ghost_bound_vertex_buffer().is_some(),
        self.ghost_bound_vertex_buffer_size()
            >= (first_vertex + vertex_count) as nat
                * self.ghost_bound_pipeline_vertex_stride() as nat,
        //  All bound resources are synchronized
        //  (omitted for brevity — same pattern as section 7)
{
    ...
}
```

The key insight is that these checks are entirely ghost-level. At runtime, `cmd_draw` compiles to a single `vkCmdDraw` call. But at verification time, Verus has checked that the descriptor set contents match the shader interface, that all referenced resources exist and are in the correct state, and that buffer sizes are sufficient. The entire class of "wrong descriptor" bugs — which in production manifests as reading from freed memory or sampling a texture in the wrong layout — is eliminated statically.

### 8.6 Command Buffer Reuse Verification

Secondary command buffers can be recorded once and re-executed in multiple primary command buffers across multiple frames. This is a performance optimization (avoid re-recording static geometry) but a correctness hazard: the secondary command buffer was recorded with assumptions about the calling context (active render pass, bound pipeline, image layouts) that may no longer hold when it's re-executed.

Caldera models this by recording the secondary command buffer's **assumptions** as ghost state:

```rust
pub ghost struct SecondaryAssumptions {
    pub requires_render_pass: bool,
    pub expected_render_pass_format: Option<RenderingInfoModel>,
    pub expected_bound_pipeline: Option<vk::Pipeline>,
    pub referenced_resources: Set<ResourceId>,
    pub required_sync_state: Map<ResourceId, SyncState>,
}
```

These assumptions are established during recording (from the `VkCommandBufferInheritanceInfo` and the commands recorded). When `cmd_execute_commands` is called on the primary command buffer, Caldera verifies that the primary's current ghost state satisfies the secondary's assumptions:

```rust
pub fn cmd_execute_commands(
    &mut self,
    secondary_buffers: &[&CommandBuffer],
)
    requires
        self.is_recording(),
        forall |i: nat| i < secondary_buffers.len() ==> {
            let sec = secondary_buffers[i];
            sec.ghost_is_executable()
            //  All referenced resources are still alive
            && forall |r| sec.ghost_assumptions().referenced_resources.contains(r) ==>
                self.ghost_resource_alive(r)
            //  Render pass compatibility (if secondary expects one)
            && sec.ghost_assumptions().requires_render_pass ==> {
                self.inside_render_pass()
                && self.ghost_rendering_info().compatible_with(
                    sec.ghost_assumptions().expected_render_pass_format.unwrap()
                )
            }
            //  Sync state satisfies secondary's requirements
            && forall |r, sync|
                sec.ghost_assumptions().required_sync_state.contains_pair(r, sync) ==> {
                    self.ghost_sync_satisfies(r, sync)
                }
        },
    ensures
        //  Ghost state updated with secondary's effects
        ...
{
    ...
}
```

This is the function-call precondition pattern: the secondary command buffer is like a function with a `requires` clause, and `cmd_execute_commands` is the call site that must satisfy it. Verus handles this naturally.

---

## 9. The Render Pass Model

Render passes deserve special attention because they are central to VR rendering and have the most complex validity rules in Vulkan.

### 9.1 Dynamic Rendering as the Primary Path

Caldera targets Vulkan 1.3+, which promoted `VK_KHR_dynamic_rendering` to core. Dynamic rendering eliminates `VkRenderPass` and `VkFramebuffer` objects entirely — you specify attachments inline at `cmd_begin_rendering` time. This dramatically simplifies the ghost model: no render pass compatibility checks, no framebuffer/render pass pairing, no subpass indexing. For the majority of VR rendering (single-pass forward shading, post-processing), dynamic rendering is strictly superior.

```rust
pub fn cmd_begin_rendering(
    &mut self,
    info: &RenderingInfo,
)
    requires
        self.is_recording(),
        !self.inside_render_pass(),
        //  All color attachments in correct layout
        forall |i: nat| i < info.color_attachments.len() ==> {
            let att = info.color_attachments[i];
            self.ghost_image_layout(att.image_view.ghost_image(), att.image_view.ghost_subresource())
                == att.image_layout
        },
        //  Depth attachment (if any) in correct layout
        info.depth_attachment.is_some() ==> {
            let att = info.depth_attachment.unwrap();
            self.ghost_image_layout(att.image_view.ghost_image(), att.image_view.ghost_subresource())
                == att.image_layout
        },
    ensures
        self.inside_render_pass(),
        self.ghost_rendering_info() == info.ghost_model(),
{
    ...
}
```

The `cmd_end_rendering` counterpart transitions attachment layouts back and exits the render pass ghost state. No subpass progression, no subpass dependencies — one begin, one end.

For the rare cases that require multi-pass rendering with input attachments (deferred shading), Caldera also supports the traditional `VkRenderPass` model described below. But the implementation roadmap prioritizes dynamic rendering first.

### 9.2 Legacy Render Pass Model (for Multi-Pass)

For multi-subpass rendering, a `RenderPass` carries a ghost model of its structure: a sequence of attachment descriptions (format, sample count, load/store ops, initial and final layouts), a sequence of subpass descriptions (which attachments are color, depth, input, resolve, and preserve attachments), and a sequence of subpass dependencies (synchronization between subpasses).

```rust
pub ghost struct RenderPassModel {
    pub attachments: Seq<AttachmentModel>,
    pub subpasses: Seq<SubpassModel>,
    pub dependencies: Seq<DependencyModel>,
}

pub ghost struct AttachmentModel {
    pub format: vk::Format,
    pub samples: u32,
    pub load_op: vk::AttachmentLoadOp,
    pub store_op: vk::AttachmentStoreOp,
    pub initial_layout: vk::ImageLayout,
    pub final_layout: vk::ImageLayout,
}

pub ghost struct SubpassModel {
    pub color_attachments: Seq<AttachmentRef>,
    pub depth_attachment: Option<AttachmentRef>,
    pub input_attachments: Seq<AttachmentRef>,
    pub resolve_attachments: Seq<AttachmentRef>,
    pub preserve_attachments: Seq<nat>,
}
```

### 9.3 Subpass Progression (Legacy Path)

When `cmd_begin_render_pass` is recorded, the builder's ghost state transitions to "inside render pass, subpass 0" and the attachment layouts transition to the layouts declared for subpass 0. When `cmd_next_subpass` is recorded, the ghost subpass index increments and attachment layouts transition to the next subpass's declared layouts. When `cmd_end_render_pass` is recorded, attachment layouts transition to their `final_layout` and the builder exits the render pass state.

Draw commands recorded during a subpass have preconditions that reference the current subpass's structure. For example, the pipeline's color attachment count must match the subpass's color attachment count, and the pipeline's depth test configuration must be compatible with whether the subpass has a depth attachment.

### 9.4 VR Stereo Rendering Pattern

For VR, the typical pattern is either two separate render passes (one per eye) or a single render pass with the `VK_KHR_multiview` extension, which renders both eyes in a single pass using a layer index. Caldera's `caldera-vr` crate provides helper types for both patterns.

The multiview path is preferred for performance (single draw call per object, single scene traversal) and has a specific ghost model: the render pass is created with a `VkRenderPassMultiviewCreateInfo` whose view masks specify which views (eyes) each subpass renders to. The ghost model tracks the view mask and verifies that framebuffer image views have the correct array layer count.

---

## 10. Integration with CuTe-RS

### 10.1 The Bridge Crate

`caldera-bridge` provides the integration point between CuTe-RS compute kernels and Caldera's command recording. The key type is `ComputeKernelHandle`, which wraps a compiled CuTe-RS kernel (SPIR-V binary) with its ghost-level resource requirements:

```rust
pub struct ComputeKernelHandle<K: CuteKernel> {
    pipeline: vk::Pipeline,
    pipeline_layout: vk::PipelineLayout,
    ghost kernel_spec: K::Spec,
}

pub trait CuteKernel {
    type Spec;

    //  Ghost: minimum buffer sizes required by this kernel
    spec fn required_buffer_sizes(&self) -> Seq<nat>;

    //  Ghost: what the kernel computes (functional spec)
    spec fn output_spec(&self, inputs: Seq<Seq<u8>>) -> Seq<Seq<u8>>;
}
```

When dispatching a CuTe-RS kernel through Caldera, the bridge function's `requires` clause checks that the bound descriptor set's buffer sizes (from Caldera's ghost model) satisfy the kernel's required buffer sizes (from CuTe-RS's ghost spec), and that the synchronization state permits compute access to all bound resources:

```rust
pub fn cmd_dispatch_cute_kernel<K: CuteKernel>(
    cmd: &mut CommandBufferBuilder,
    kernel: &ComputeKernelHandle<K>,
    descriptor_set: &DescriptorSet,
    group_count_x: u32,
    group_count_y: u32,
    group_count_z: u32,
)
    requires
        cmd.is_recording(),
        !cmd.inside_render_pass(),
        cmd.ghost_bound_compute_pipeline() == Some(kernel.pipeline),
        //  CuTe-RS buffer size requirements met by Caldera's buffer model
        forall |i: nat| i < kernel.ghost_kernel_spec.required_buffer_sizes().len() ==> {
            descriptor_set.ghost_binding_buffer_size(i)
                >= kernel.ghost_kernel_spec.required_buffer_sizes().index(i)
        },
        //  All bound buffers are synchronized for compute access
        forall |i: nat| i < descriptor_set.ghost_binding_count() ==> {
            cmd.ghost_sync.readable_or_writable(
                descriptor_set.ghost_binding_resource(i),
                PipelineStage::COMPUTE_SHADER,
            )
        },
    ensures
        //  Sync state updated: output buffers now have a pending write at COMPUTE_SHADER
        forall |i: nat| kernel.ghost_kernel_spec.is_output(i) ==> {
            cmd.ghost_sync.last_write(descriptor_set.ghost_binding_resource(i))
                == Some(SyncPoint {
                    stage: PipelineStage::COMPUTE_SHADER,
                    ..
                })
        },
        //  Input buffers: sync state unchanged (read-only access)
        forall |i: nat| kernel.ghost_kernel_spec.is_input_only(i) ==> {
            cmd.ghost_sync.last_reads(descriptor_set.ghost_binding_resource(i))
                == old(cmd).ghost_sync.last_reads(
                    descriptor_set.ghost_binding_resource(i)
                ).insert(SyncPoint { stage: PipelineStage::COMPUTE_SHADER, .. })
        },
        //  Functional correctness (Tier 2 — only when kernel provides output_spec):
        kernel.ghost_kernel_spec.has_functional_spec() ==> {
            forall |i: nat| kernel.ghost_kernel_spec.is_output(i) ==> {
                cmd.ghost_buffer_contents(descriptor_set.ghost_binding_resource(i))
                    == kernel.ghost_kernel_spec.output_spec(
                        old(cmd).ghost_input_contents(descriptor_set)
                    ).index(i)
            }
        },
{
    ...
}
```

The ensures clause has two tiers of guarantees:

**Tier 1 (always verified):** Buffer sizes are sufficient, synchronization is correct, and the sync state is properly updated after dispatch. This is Caldera's core value — no GPU undefined behavior. Every kernel dispatch gets this regardless of how the kernel is defined.

**Tier 2 (opt-in functional correctness):** When a CuTe-RS kernel provides a functional specification (`output_spec`), Caldera threads it through — the ensures clause additionally guarantees that output buffers contain the specified result. This is the end-to-end story: CuTe-RS verifies the kernel implements `output_spec`, Caldera verifies correct dispatch, and the combined guarantee covers correctness from input to output. But this is opt-in. Many kernels (particle systems, physics simulations, procedural generation) are hard to specify functionally, and forcing a full `output_spec` on every kernel would make the system impractical. For those kernels, Tier 1 is still a strong guarantee — you know the dispatch is safe even if you can't state what it computes.

### 10.2 Buffer Lifecycle Example

To make this concrete, here is a simplified verified lifecycle for a compute-then-render workflow:

```rust
//  1. Create buffers (ghost: size established, sync state = initial)
let vertex_buffer = caldera.create_buffer(size, VERTEX | STORAGE | TRANSFER_DST)?;
let uniform_buffer = caldera.create_buffer(size, UNIFORM | TRANSFER_DST)?;

//  2. Upload initial data via staging (ghost: sync state = TRANSFER write)
cmd.cmd_copy_buffer(&staging, &vertex_buffer, &[region])?;

//  3. Barrier: TRANSFER → COMPUTE (ghost: sync advanced, vertex_buffer readable at COMPUTE)
cmd.cmd_pipeline_barrier(&barrier!(
    buffer: vertex_buffer,
    src: TRANSFER_WRITE,
    dst: COMPUTE_SHADER_READ | COMPUTE_SHADER_WRITE,
));

//  4. CuTe-RS kernel modifies vertex positions (ghost: output_spec applied, write at COMPUTE)
cmd.cmd_dispatch_cute_kernel(&skin_kernel, &desc_set, groups_x, 1, 1)?;

//  5. Barrier: COMPUTE → VERTEX_INPUT (ghost: sync advanced, vertex_buffer readable at VERTEX)
cmd.cmd_pipeline_barrier(&barrier!(
    buffer: vertex_buffer,
    src: COMPUTE_SHADER_WRITE,
    dst: VERTEX_ATTRIBUTE_READ,
));

//  6. Render pass uses vertex buffer (ghost: precondition met by barrier in step 5)
cmd.cmd_begin_render_pass(&rp_info, SubpassContents::INLINE)?;
cmd.cmd_bind_vertex_buffers(0, &[&vertex_buffer], &[0])?;
cmd.cmd_draw(vertex_count, 1, 0, 0)?;
cmd.cmd_end_render_pass()?;
```

If you remove step 5 (the barrier between compute and vertex input), Verus will reject the program because `cmd_draw` requires `ghost_sync.readable(vertex_buffer, VERTEX_INPUT)`, and without the barrier, the last known access is a compute shader write with no subsequent barrier to the vertex input stage. The error is caught at verification time, not at runtime.

---

## 11. Render Graph Verification

### 11.1 Why Verify the Render Graph

Modern rendering engines organize each frame as a directed acyclic graph (DAG) of render passes: the shadow pass writes a depth map, the geometry pass reads it and writes the G-buffer, the lighting pass reads the G-buffer and writes the final color, post-processing reads the final color and writes to the swapchain. This structure is called the render graph, and getting it wrong is a major source of bugs — missing dependencies cause synchronization hazards, cycles cause deadlocks or infinite loops in the graph executor, and unused passes waste GPU time.

Caldera can verify the render graph at the spec level, then verify that the actual command recording faithfully implements it. This is **architectural verification** — not just "each command is individually valid" but "the overall structure of the frame is correct."

### 11.2 The Spec-Level Render Graph

A render graph is defined as a spec-level DAG:

```rust
pub ghost struct RenderGraph {
    pub passes: Seq<RenderPassNode>,
    pub edges: Seq<ResourceEdge>,
}

pub ghost struct RenderPassNode {
    pub id: nat,
    pub name: Seq<char>,       //  For diagnostics
    pub reads: Set<ResourceId>,
    pub writes: Set<ResourceId>,
    pub pass_type: PassType,   //  Graphics, Compute, Transfer
}

pub ghost struct ResourceEdge {
    pub from_pass: nat,        //  Writer pass ID
    pub to_pass: nat,          //  Reader pass ID
    pub resource: ResourceId,
    pub src_layout: vk::ImageLayout,  //  Layout after write
    pub dst_layout: vk::ImageLayout,  //  Layout needed by reader
}

pub ghost enum PassType {
    Graphics { color_attachments: nat, has_depth: bool },
    Compute { dispatch_groups: (nat, nat, nat) },
    Transfer,
}
```

Spec functions verify structural properties:

```rust
///  The render graph contains no cycles.
pub open spec fn is_acyclic(graph: &RenderGraph) -> bool {
    //  Topological ordering exists
    exists |order: Seq<nat>| {
        order.len() == graph.passes.len()
        && order.is_permutation_of(graph.pass_ids())
        && forall |e: &ResourceEdge| graph.edges.contains(e) ==> {
            order.index_of(e.from_pass) < order.index_of(e.to_pass)
        }
    }
}

///  Every resource read by a pass is either written by an earlier pass
///  (connected by an edge) or is an external input.
pub open spec fn all_dependencies_satisfied(
    graph: &RenderGraph,
    external_inputs: Set<ResourceId>,
) -> bool {
    forall |p: &RenderPassNode| graph.passes.contains(p) ==> {
        forall |r| p.reads.contains(r) ==> {
            external_inputs.contains(r)
            || exists |e: &ResourceEdge| {
                graph.edges.contains(e)
                && e.to_pass == p.id
                && e.resource == r
            }
        }
    }
}

///  No two passes write to the same resource without an ordering edge.
pub open spec fn no_write_conflicts(graph: &RenderGraph) -> bool {
    forall |p1: &RenderPassNode, p2: &RenderPassNode|
        graph.passes.contains(p1) && graph.passes.contains(p2) && p1.id != p2.id ==> {
            forall |r| p1.writes.contains(r) && p2.writes.contains(r) ==> {
                //  There must be an ordering between p1 and p2
                graph.reachable(p1.id, p2.id) || graph.reachable(p2.id, p1.id)
            }
        }
}
```

### 11.3 Verified Graph Execution

The render graph executor records actual Vulkan commands. It takes a verified `RenderGraph` and produces a command buffer. The executor function's `requires` clause demands the graph is well-formed:

```rust
pub fn execute_render_graph(
    cmd: &mut CommandBufferBuilder,
    graph: &RenderGraph,
    resources: &ResourceMap,
)
    requires
        cmd.is_recording(),
        is_acyclic(graph),
        all_dependencies_satisfied(graph, resources.ghost_external_inputs()),
        no_write_conflicts(graph),
        //  All resources referenced by the graph exist and are alive
        forall |r| graph.all_resources().contains(r) ==>
            resources.ghost_resource_alive(r),
    ensures
        //  All passes have been recorded in a valid topological order
        //  All inter-pass barriers are present for each edge
        //  All resources end in their expected final layouts
        forall |e: &ResourceEdge| graph.edges.contains(e) ==> {
            cmd.ghost_barrier_exists_for_edge(e)
        },
{
    //  Topologically sort passes, record each pass's commands,
    //  insert barriers between passes based on edges
    ...
}
```

The loop that iterates over passes in topological order carries an invariant that all previously-recorded passes have had their output barriers inserted:

```rust
let topo_order = topological_sort(graph);
let mut i: usize = 0;
while i < topo_order.len()
    invariant
        //  All passes [0, i) have been recorded with correct barriers
        forall |j: nat| j < i as nat ==> {
            let pass = graph.passes[topo_order[j]];
            cmd.ghost_pass_recorded(pass)
            && forall |e: &ResourceEdge|
                graph.edges.contains(e) && e.from_pass == pass.id
                && order.index_of(e.to_pass) < i as nat ==> {
                    cmd.ghost_barrier_exists_for_edge(e)
                }
        },
{
    let pass = &graph.passes[topo_order[i]];
    //  Record barriers for incoming edges
    record_incoming_barriers(cmd, graph, pass);
    //  Record pass commands
    record_pass(cmd, graph, pass, resources);
    i += 1;
}
```

This gives you a two-level guarantee: the render graph structure is correct (acyclic, complete, conflict-free), and the command recording faithfully implements the graph (correct order, correct barriers). Refactoring the render graph — adding a pass, reordering passes, changing resource dependencies — is checked by Verus. You change the graph definition, and Verus tells you if the structural properties still hold and if the executor still implements the graph correctly.

---

## 12. The VR-Specific Layer

### 12.1 Frame Pacing Model

VR rendering has a hard real-time constraint: each frame must be submitted before the display's vsync deadline, or the compositor will reproject a stale frame, causing visible judder. Caldera's VR layer models this constraint in the ghost state.

The `FrameContext` type represents a single frame's rendering lifecycle. It carries a ghost deadline (the timestamp by which `vkQueuePresentKHR` must complete) and tracks the ghost "time budget" consumed by recorded work. The time budget is an abstract, conservative estimate based on the number of draw calls, compute dispatches, and barrier stalls. This is not a cycle-accurate performance model — that would be impossible to verify and hardware-dependent. Instead, it's a coarse resource budget that catches obvious overcommitment (recording 10,000 draw calls in a frame that can handle 1,000).

The budget model is explicitly optional and behind a feature flag. Its value is in catching architectural mistakes ("you're recording an entire frame's worth of work twice because you forgot to check a flag"), not in fine-grained performance tuning.

### 12.2 OpenXR Integration

The `openxr.rs` module provides glue between Caldera and the OpenXR runtime. OpenXR provides the VR session, the swapchain images, and the frame timing. Caldera provides verified command recording. The integration point is the swapchain image: OpenXR gives you a `VkImage` handle, and Caldera wraps it with ghost state (format, extent, layout, sync state). The ghost state is established from the OpenXR swapchain creation parameters, which are known at compile time.

The key safety property here is that the OpenXR swapchain image is in `VK_IMAGE_LAYOUT_COLOR_ATTACHMENT_OPTIMAL` when acquired and must be transitioned back before release. Caldera's ghost model tracks this and ensures you don't release a swapchain image in the wrong layout.

### 12.3 Reprojection Safety

If the application misses its frame deadline, the VR compositor performs asynchronous reprojection — it takes the previous frame and warps it based on updated head tracking to reduce perceived latency. This is handled by the runtime, not the application. But the application must cooperate by submitting depth information and motion vectors that the compositor uses for reprojection.

Caldera's VR layer can optionally verify that the application's render pass includes the depth and motion vector outputs that the compositor requires. This is a simple check on the render pass model's attachment descriptions, but it catches a real class of bugs (forgetting the depth output means the compositor falls back to rotational-only reprojection, which produces translation smear).

### 12.4 Frame Completeness

A VR frame is only correct if both eyes are rendered. An early return, an exception path, or a conditional branch that skips one eye's render pass produces a frame where one eye sees a stale image from the previous frame. This is immediately noticeable and physically uncomfortable — the visual cortex expects binocular consistency and reacts to violations with nausea.

Caldera's VR layer tracks frame completeness with ghost state on the `FrameContext`:

```rust
pub struct FrameContext {
    ghost views_rendered: Set<nat>,  //  Which views (eyes) have been rendered
    ghost view_count: nat,           //  Total views expected (2 for stereo)
    ghost frame_id: nat,
}
```

Each render submission that writes to a view's swapchain image adds to `views_rendered`. The `end_frame` function (which wraps OpenXR's `xrEndFrame`) requires completeness:

```rust
pub fn end_frame(
    frame: &FrameContext,
    swapchain: &Swapchain,
)
    requires
        //  Every view must have been rendered this frame
        frame.ghost_views_rendered.len() == frame.ghost_view_count,
        forall |v: nat| v < frame.ghost_view_count ==>
            frame.ghost_views_rendered.contains(v),
        //  Swapchain images for all views are in Rendered state
        forall |v: nat| v < frame.ghost_view_count ==> {
            swapchain.ghost_image_state(v).is_rendered()
            && swapchain.ghost_image_state(v).frame_id() == frame.ghost_frame_id
        },
{
    ...
}
```

If any code path can reach `end_frame` without rendering both eyes, Verus rejects it. The programmer must either render both eyes on every path or explicitly handle the skip case (e.g., by submitting a black frame for the missing eye, which still counts as "rendered").

For multiview rendering (both eyes in a single render pass), the render pass itself marks both views as rendered in one shot:

```rust
//  After cmd_end_rendering with a multiview pass covering views 0 and 1:
ensures
    frame.ghost_views_rendered == old(frame).ghost_views_rendered
        .insert(0).insert(1),
```

### 12.5 Deterministic Stereo Rendering

A subtle VR bug occurs when the two eye renders see different scene state. If a uniform buffer is updated between the left eye render and the right eye render, one eye sees frame N's data and the other sees frame N+1's data. The result is a single frame of binocular inconsistency — objects appear to "jump" between eyes. This is a data race at the application level, not the GPU level, and no amount of Vulkan synchronization prevents it.

Caldera verifies stereo consistency by tracking the **data generation** of uniform and storage buffers used in rendering:

```rust
pub ghost struct BufferGeneration {
    pub generation: nat,        //  Monotonically increasing on each write
    pub last_writer: Seq<char>, //  Identifies the write source (for diagnostics)
}
```

Every buffer write (via staging copy, compute dispatch, or mapped memory write) increments the ghost generation. The stereo rendering verification requires that both eyes see the same generation of every shared buffer:

```rust
pub fn render_stereo_frame(
    cmd: &mut CommandBufferBuilder,
    frame: &mut FrameContext,
    scene: &SceneResources,
)
    requires
        //  Scene data is finalized — no writes pending between eye renders
        scene.ghost_uniform_buffer_generation() == scene.ghost_frame_generation(),
        //  Both eye view matrices are available
        frame.ghost_view_matrices_set(),
    ensures
        frame.ghost_views_rendered.contains(0)
        && frame.ghost_views_rendered.contains(1)
        //  Both eyes saw the same buffer generation
        && frame.ghost_left_eye_data_generation()
            == frame.ghost_right_eye_data_generation()
{
    //  Record left eye render
    //  Record right eye render (or use multiview)
    ...
}
```

The key precondition is `scene.ghost_uniform_buffer_generation() == scene.ghost_frame_generation()` — the scene data must be finalized before either eye render begins. If you try to update uniforms between eye renders, the ghost generation increments and the postcondition `left_generation == right_generation` would fail.

For multiview rendering, stereo consistency is guaranteed trivially — both eyes are rendered by the same draw calls reading the same buffer contents. The generation check is still useful for the setup phase: it verifies that all scene updates are complete before the single multiview pass begins.

---

## 13. Verified Asset Pipeline

### 13.1 The Problem

Mesh data arrives from external sources — artist-authored files, procedural generation, network streams. By the time it reaches the GPU as vertex and index buffers, it's just bytes. If the data is malformed (degenerate triangles, out-of-range bone indices, non-normalized weights, mismatched vertex/index counts, incorrect winding order), the GPU renders garbage or hangs. Validation layers don't check application data, only Vulkan API usage. And the bug manifests far from its source — the draw call succeeds but produces a visual artifact that's traced back hours later to a mesh loading bug.

The verus-topology and verus-geometry crates already prove structural invariants on meshes (half-edge validity, consistent orientation, Euler characteristic). Caldera can require those invariants as preconditions on GPU upload, closing the gap between verified mesh construction and verified rendering.

### 13.2 Ghost Mesh Invariants on Buffers

When mesh data is uploaded to a GPU buffer, the buffer carries a ghost model of the mesh's structural properties:

```rust
pub ghost struct MeshBufferInvariants {
    pub vertex_count: nat,
    pub index_count: nat,
    pub vertex_stride: nat,
    pub index_type: vk::IndexType,   //  UINT16 or UINT32
    pub has_normals: bool,
    pub has_tangents: bool,
    pub bone_count: Option<nat>,     //  For skinned meshes
    //  Structural invariants
    pub all_indices_in_range: bool,  //  Every index < vertex_count
    pub no_degenerate_triangles: bool,
    pub consistent_winding: bool,
    pub normalized_weights: bool,    //  Bone weights sum to 1.0
    //  From verus-topology
    pub structurally_valid: bool,    //  Half-edge mesh invariants hold
    pub euler_characteristic: int,   //  V - E + F
    pub is_closed: bool,            //  No boundary edges
}
```

The upload function threads these invariants from the CPU-side mesh to the GPU buffer:

```rust
pub fn upload_mesh<M: VerifiedMesh>(
    cmd: &mut CommandBufferBuilder,
    staging: &Buffer,
    vertex_buffer: &mut Buffer,
    index_buffer: &mut Buffer,
    mesh: &M,
)
    requires
        cmd.is_recording(),
        //  Mesh satisfies structural invariants (from verus-topology)
        mesh.ghost_structurally_valid(),
        mesh.ghost_all_indices_in_range(),
        //  Buffers are large enough
        vertex_buffer.ghost_size >= mesh.ghost_vertex_count() * mesh.ghost_vertex_stride(),
        index_buffer.ghost_size >= mesh.ghost_index_count() * mesh.ghost_index_size(),
        //  Standard sync requirements
        cmd.ghost_sync.writable(vertex_buffer, PipelineStage::TRANSFER),
        cmd.ghost_sync.writable(index_buffer, PipelineStage::TRANSFER),
    ensures
        //  Ghost mesh invariants are now on the GPU buffers
        vertex_buffer.ghost_mesh_invariants == Some(MeshBufferInvariants {
            vertex_count: mesh.ghost_vertex_count(),
            index_count: mesh.ghost_index_count(),
            vertex_stride: mesh.ghost_vertex_stride(),
            all_indices_in_range: true,
            no_degenerate_triangles: mesh.ghost_no_degenerate_triangles(),
            consistent_winding: mesh.ghost_consistent_winding(),
            structurally_valid: true,
            ..
        }),
{
    ...
}
```

### 13.3 Draw-Time Mesh Validation

The ghost mesh invariants flow through to draw calls. When `cmd_draw_indexed` is called, the precondition checks that the bound index buffer's indices are all in range:

```rust
pub fn cmd_draw_indexed(
    &mut self,
    index_count: u32,
    instance_count: u32,
    first_index: u32,
    vertex_offset: i32,
    first_instance: u32,
)
    requires
        self.is_recording(),
        self.inside_render_pass(),
        self.ghost_bound_graphics_pipeline().is_some(),
        self.ghost_bound_index_buffer().is_some(),
        //  Index buffer has mesh invariants attached
        self.ghost_bound_index_buffer_mesh_invariants().is_some(),
        //  All indices are in range of the vertex buffer
        self.ghost_bound_index_buffer_mesh_invariants().unwrap().all_indices_in_range,
        //  Index count within the index buffer's bounds
        (first_index + index_count) as nat
            <= self.ghost_bound_index_buffer_mesh_invariants().unwrap().index_count,
        //  Vertex offset doesn't push indices out of range
        vertex_offset >= 0 ==> {
            self.ghost_bound_index_buffer_mesh_invariants().unwrap().vertex_count
                + vertex_offset as nat
                <= self.ghost_bound_vertex_buffer_vertex_count()
        },
        //  ... standard descriptor set and sync requirements
{
    ...
}
```

This closes a real gap: a mesh with an out-of-range index causes the GPU to read from arbitrary memory. In the best case this is garbage vertices; in the worst case it's a security vulnerability (information disclosure via rendered pixels). By threading the `all_indices_in_range` invariant from mesh construction through upload through draw, Caldera proves this can't happen.

### 13.4 Cross-Crate Invariant Threading

The verified asset pipeline is the first concrete example of cross-crate ghost invariant composition. The `VerifiedMesh` trait bridges verus-topology's mesh model to Caldera's buffer model:

```rust
pub trait VerifiedMesh {
    //  From verus-topology
    spec fn ghost_structurally_valid(&self) -> bool;
    spec fn ghost_all_indices_in_range(&self) -> bool;
    spec fn ghost_consistent_winding(&self) -> bool;
    spec fn ghost_no_degenerate_triangles(&self) -> bool;
    spec fn ghost_euler_characteristic(&self) -> int;

    //  Geometry (from verus-geometry)
    spec fn ghost_vertex_count(&self) -> nat;
    spec fn ghost_index_count(&self) -> nat;
    spec fn ghost_vertex_stride(&self) -> nat;
    spec fn ghost_index_size(&self) -> nat;

    //  Serialization: the byte representation preserves invariants
    proof fn lemma_serialization_preserves_invariants(&self)
        requires self.ghost_structurally_valid()
        ensures self.as_bytes().ghost_deserializes_to_valid_mesh();
}
```

An implementation of `VerifiedMesh` for verus-topology's `HalfEdgeMesh` would carry the proofs that the mesh's half-edge structure implies `all_indices_in_range` (since every face references vertices by index into the vertex array, and `structurally_valid` implies all indices are < vertex count). The proof exists in verus-topology already — it's the `index_bounds` conjunct of `structurally_valid`.

---

## 14. Temporal Invariants and Multi-Frame Verification

### 14.1 Beyond Single-Frame Correctness

Sections 6–12 verify properties within a single frame or submission. But many rendering bugs only manifest over time: memory grows imperceptibly until OOM, an animation parameter accumulates floating-point error until it wraps, a ring buffer index desynchronizes once every 2^16 frames. These are temporal bugs — the system is correct at any single instant but incorrect over its lifetime.

Verus's loop invariants are the natural tool for temporal verification. The main render loop is a `while` loop, and its invariant can express properties that must hold across all frames.

### 14.2 Memory Stability

The simplest temporal invariant: resource counts don't grow.

```rust
let mut frame_id: u64 = 0;
while running
    invariant
        //  Resource counts are bounded
        device.ghost_live_buffers <= BUFFER_POOL_SIZE,
        device.ghost_live_images <= IMAGE_POOL_SIZE,
        //  GPU memory usage is stable
        forall |h: nat| h < device.ghost_heap_count() ==> {
            device.ghost_heap_usage[h] <= device.ghost_heap_budget[h]
        },
        //  Frame counter doesn't overflow (u64 won't in practice, but Verus proves it)
        frame_id < u64::MAX,
        //  In-flight frame count bounded
        device.ghost_pending_submissions.len() <= MAX_IN_FLIGHT_FRAMES,
{
    //  ... frame logic ...
    frame_id = frame_id + 1;
}
```

If any code path inside the loop allocates a buffer without freeing one, the `ghost_live_buffers <= BUFFER_POOL_SIZE` invariant is violated and Verus rejects the program. This catches the "one leaked buffer every N frames" bug class that is nearly impossible to detect with runtime tools until the application has been running for hours.

### 14.3 Ring Buffer Correctness

Triple-buffered rendering uses a ring buffer of frame resources (command buffers, descriptor pools, per-frame uniforms). The ring buffer index advances each frame and wraps modulo the buffer count. Getting the modular arithmetic wrong causes a frame to overwrite resources that are still in use by a previous frame's GPU work.

```rust
pub ghost struct RingBuffer<const N: usize> {
    pub write_head: nat,    //  Next frame to write
    pub read_head: nat,     //  Oldest frame still in flight
    pub frames_in_flight: nat,
}

//  Main loop invariant includes:
invariant
    ring.ghost_frames_in_flight <= MAX_IN_FLIGHT_FRAMES,
    ring.ghost_frames_in_flight == (ring.ghost_write_head - ring.ghost_read_head) % N,
    //  The write slot is not still in flight
    ring.ghost_write_head % N != ring.ghost_read_head % N
        || ring.ghost_frames_in_flight == 0,
    //  Each in-flight frame's resources are not aliased
    forall |i: nat, j: nat|
        i < ring.ghost_frames_in_flight && j < ring.ghost_frames_in_flight && i != j ==> {
            (ring.ghost_read_head + i) % N != (ring.ghost_read_head + j) % N
        },
```

The fence-wait at the start of each frame advances `read_head`, which the invariant proves frees exactly one slot for `write_head`. If the modular arithmetic is wrong — e.g., using `% (N-1)` instead of `% N` — Verus catches it.

### 14.4 Animation Continuity

Temporal coherence in animation requires that interpolation parameters change smoothly between frames. A discontinuity (parameter jumping from 0.99 to 0.0 without wrapping correctly) causes visible popping. Caldera can verify continuity:

```rust
//  Animation loop invariant
invariant
    //  Parameter is in valid range
    anim_t >= RationalModel::from_int_spec(0),
    anim_t.lt(RationalModel::from_int_spec(1)),
    //  Delta is bounded (no sudden jumps)
    anim_delta.le(max_delta),
    anim_delta.ge(RationalModel::from_int_spec(0)),
    //  Wraparound is explicit and correct
    anim_t.add(anim_delta).ge(RationalModel::from_int_spec(1)) ==> {
        next_anim_t.eqv(anim_t.add(anim_delta).sub(RationalModel::from_int_spec(1)))
    },
    anim_t.add(anim_delta).lt(RationalModel::from_int_spec(1)) ==> {
        next_anim_t.eqv(anim_t.add(anim_delta))
    },
```

This uses the verus-algebra `Rational` type for exact arithmetic, avoiding the floating-point error accumulation that causes animation drift over long sessions. For VR where sessions can last hours, this matters.

---

## 15. Information Flow Control for Social VR

### 15.1 The Privacy Problem

Social VR is uniquely sensitive. The headset captures intimate biometric data — eye tracking, hand poses, body kinematics, facial expressions, room geometry. This data drives the user's avatar rendering. In a multiplayer session, each player's private data must render only on their own display. If player A's eye gaze direction accidentally feeds into the shader that renders player A's avatar on player B's screen, player B can infer where player A is looking — a serious privacy violation.

This is not a hypothetical concern. Avatar rendering systems are complex, with shared buffers, instanced draw calls, and compute-driven animation. A bug that copies one player's tracking data into another player's uniform buffer is easy to write and hard to detect — it produces visually plausible output (the avatar moves, just with the wrong person's data).

### 15.2 Ghost Taint Labels

Caldera models information flow with ghost taint labels on every buffer and image:

```rust
pub ghost enum TaintLabel {
    Public,                         //  Safe for any player to see
    PlayerPrivate { player_id: nat }, //  Only visible to this player
    SessionPrivate,                 //  Visible to all players in session, not outside
    ServerOnly,                     //  Never rendered, only used for server-side logic
}

pub ghost struct TaintSet {
    pub labels: Set<TaintLabel>,
}
```

Every buffer and image carries a `ghost taint: TaintSet`. The rules are:

1. **Write propagation:** Writing data with taint T to a buffer taints the buffer with T. If player 1's hand tracking data (tainted `PlayerPrivate(1)`) is copied to a uniform buffer, that buffer becomes tainted `PlayerPrivate(1)`.

2. **Compute propagation:** A compute dispatch that reads from a tainted input buffer taints all output buffers with the union of input taints. If a skinning kernel reads from both a shared skeleton buffer (`Public`) and a player-specific pose buffer (`PlayerPrivate(1)`), the output vertex buffer is tainted `PlayerPrivate(1)`.

3. **Render restriction:** Rendering to a swapchain image for player P requires that all read resources are either `Public` or `PlayerPrivate(P)`. Reading a `PlayerPrivate(Q)` resource where Q != P is a verification error.

```rust
pub fn cmd_draw_for_player(
    &mut self,
    player_id: nat,
    vertex_count: u32,
    instance_count: u32,
    first_vertex: u32,
    first_instance: u32,
)
    requires
        self.is_recording(),
        self.inside_render_pass(),
        //  The render target is this player's swapchain
        self.ghost_current_render_target_owner() == player_id,
        //  ALL resources read by this draw are visible to this player
        forall |r| self.ghost_draw_reads().contains(r) ==> {
            let taint = self.ghost_resource_taint(r);
            taint.visible_to(player_id)
        },
{
    ...
}

pub open spec fn visible_to(taint: &TaintSet, player_id: nat) -> bool {
    forall |label| taint.labels.contains(label) ==> {
        match label {
            TaintLabel::Public => true,
            TaintLabel::SessionPrivate => true,
            TaintLabel::PlayerPrivate { player_id: pid } => pid == player_id,
            TaintLabel::ServerOnly => false,
        }
    }
}
```

### 15.3 Taint Propagation Through Compute

The CuTe-RS bridge (section 10) already tracks which buffers are inputs and outputs of a kernel dispatch. Taint propagation is a natural extension:

```rust
//  In cmd_dispatch_cute_kernel ensures clause:
ensures
    //  Output taint = union of input taints
    forall |i: nat| kernel.ghost_kernel_spec.is_output(i) ==> {
        let output_resource = descriptor_set.ghost_binding_resource(i);
        self.ghost_resource_taint(output_resource) == TaintSet {
            labels: union_of_input_taints(
                kernel,
                descriptor_set,
                old(self),
            )
        }
    },
```

Where `union_of_input_taints` collects the taints of all input buffers:

```rust
pub open spec fn union_of_input_taints<K: CuteKernel>(
    kernel: &ComputeKernelHandle<K>,
    descriptor_set: &DescriptorSet,
    cmd_state: &CommandBufferBuilder,
) -> Set<TaintLabel> {
    Set::new(|label| exists |i: nat| {
        kernel.ghost_kernel_spec.is_input(i)
        && cmd_state.ghost_resource_taint(
            descriptor_set.ghost_binding_resource(i)
        ).labels.contains(label)
    })
}
```

### 15.4 Practical Impact

This is standard information flow control (IFC) applied to GPU resources — a well-understood technique from security research, but novel in the context of GPU rendering. The ghost taint tracking adds no runtime overhead, and the verification cost is modest (ghost set membership is simple for Z3).

The practical workflow: the developer annotates buffer creation with taint labels (player tracking data gets `PlayerPrivate`, shared world geometry gets `Public`), and Verus propagates taints automatically through copies, compute dispatches, and barrier operations. If any code path could render one player's private data on another player's screen, Verus rejects it.

For non-social applications (single-player VR, desktop rendering), the taint system is simply not used — all resources default to `Public` and the `visible_to` precondition is trivially satisfied.

---

## 16. Cross-Crate End-to-End Composition

### 16.1 The Full Pipeline

The verus-cad workspace contains four verified crate families that, together, span the full rendering pipeline:

```
verus-topology (mesh construction, topological invariants)
    → verus-geometry (geometric predicates, intersection tests)
        → CuTe-RS (GPU compute kernels, layout algebra)
            → Caldera (Vulkan command recording, synchronization)
```

Each crate currently verifies in isolation. But the ghost invariants at each crate's boundary can be composed to create an end-to-end verified pipeline from mesh construction to rendered pixels.

### 16.2 Invariant Threading Across Crate Boundaries

The key mechanism is **ghost spec traits** that cross crate boundaries. Each crate defines what it guarantees about its output, and the next crate in the pipeline requires that guarantee as input:

```rust
//  verus-topology guarantees:
ensures
    mesh.structurally_valid()
    && mesh.euler_characteristic() == 2  //  Topological sphere
    && mesh.is_closed()

//  verus-geometry adds:
ensures
    mesh.consistently_oriented()
    && mesh.no_degenerate_triangles()

//  Asset upload (Caldera) requires:
requires
    mesh.ghost_structurally_valid()
    && mesh.ghost_consistently_oriented()
    && mesh.ghost_no_degenerate_triangles()
ensures
    vertex_buffer.ghost_mesh_invariants.structurally_valid == true

//  CuTe-RS skinning kernel requires:
requires
    input_buffer.ghost_mesh_invariants.vertex_count > 0
    && input_buffer.ghost_mesh_invariants.all_indices_in_range
ensures
    //  Vertex count preserved, positions modified but count unchanged
    output_buffer.ghost_mesh_invariants.vertex_count
        == input_buffer.ghost_mesh_invariants.vertex_count
    && output_buffer.ghost_mesh_invariants.all_indices_in_range
        == input_buffer.ghost_mesh_invariants.all_indices_in_range

//  Caldera draw requires:
requires
    vertex_buffer.ghost_mesh_invariants.all_indices_in_range
    && vertex_buffer.ghost_mesh_invariants.vertex_count > 0
```

A topology bug in mesh construction — say, `from_face_cycles` produces a mesh where one face references a vertex index that's out of range — would cause `mesh.ghost_structurally_valid()` to be false (since `index_bounds` is a conjunct of `structurally_valid`). This propagates: the upload function's `requires` clause fails, the CuTe-RS dispatch's `requires` clause fails, and the draw call's `requires` clause fails. The bug is caught at the earliest possible point — the mesh construction — even though the symptom would only be visible at the draw call.

### 16.3 Verified GPU Readback

When GPU-computed results are read back to the CPU (for physics feedback, analytics, screenshot capture, or network replication), the ghost model must carry through the readback path. This is the reverse direction of the asset pipeline: GPU buffer → staging buffer → mapped memory → CPU data.

```rust
pub fn cmd_copy_buffer_to_staging(
    cmd: &mut CommandBufferBuilder,
    gpu_buffer: &Buffer,
    staging_buffer: &mut Buffer,
    region: &BufferCopy,
)
    requires
        cmd.is_recording(),
        gpu_buffer.ghost_is_bound(),
        staging_buffer.ghost_is_bound(),
        staging_buffer.ghost_host_visible,
        cmd.ghost_sync.readable(gpu_buffer, PipelineStage::TRANSFER),
        cmd.ghost_sync.writable(staging_buffer, PipelineStage::TRANSFER),
    ensures
        //  Staging buffer inherits GPU buffer's ghost contents
        staging_buffer.ghost_contents_at(region.dst_offset, region.size)
            == gpu_buffer.ghost_contents_at(region.src_offset, region.size),
        //  And inherits taint labels
        staging_buffer.ghost_taint == gpu_buffer.ghost_taint,
{
    ...
}

pub fn map_memory_and_read(
    device: &Device,
    staging_buffer: &Buffer,
    offset: usize,
    size: usize,
) -> &[u8]
    requires
        staging_buffer.ghost_host_visible,
        staging_buffer.ghost_is_bound(),
        //  Must have waited for all GPU writes to complete
        device.ghost_no_pending_writes_to(staging_buffer),
        offset + size <= staging_buffer.ghost_size as usize,
    ensures
        //  The returned bytes match the ghost model
        result.len() == size,
        result@ == staging_buffer.ghost_contents_at(offset as nat, size as nat),
{
    ...
}
```

The full readback path is: GPU compute writes to buffer (ghost contents set by CuTe-RS output_spec) → barrier → copy to staging (ghost contents preserved) → fence wait (pending writes cleared) → map (bytes match ghost model). If the CuTe-RS kernel has a tier 2 functional spec, the CPU-side code receives data that is provably the result of the specified computation. This is end-to-end: from kernel spec to CPU bytes, verified.

---

## 17. Verified Hot-Reload

### 17.1 Runtime Pipeline Replacement

During VR development (and increasingly in production for live events), shaders and pipelines are replaced at runtime without restarting the application. This is hot-reload: compile a new shader, swap it into the running renderer, see the result immediately. The danger is that the new shader may be incompatible with the existing pipeline layout, descriptor sets, or vertex input state. In unverified code, this produces a crash or garbage rendering. With Caldera, the hot-reload operation has verified preconditions.

### 17.2 Compatibility Verification

```rust
pub fn hot_reload_graphics_pipeline(
    device: &Device,
    old_pipeline: &Pipeline,
    new_vertex_shader: Option<&ShaderModule>,
    new_fragment_shader: Option<&ShaderModule>,
) -> Result<Pipeline>
    requires
        //  If replacing vertex shader: descriptor bindings must be compatible
        new_vertex_shader.is_some() ==> {
            let new_if = new_vertex_shader.unwrap().ghost_interface();
            let old_if = old_pipeline.ghost_vertex_shader_interface();
            //  Same descriptor set layout requirements
            new_if.descriptor_bindings == old_if.descriptor_bindings
            //  Same or compatible push constant range
            && new_if.push_constant_range.compatible_with(old_if.push_constant_range)
            //  Vertex inputs: same locations, compatible formats
            && forall |i: nat| i < new_if.inputs.len() ==> {
                exists |j: nat| j < old_if.inputs.len() && {
                    old_if.inputs[j].location == new_if.inputs[i].location
                    && format_compatible(old_if.inputs[j].format, new_if.inputs[i].format)
                }
            }
        },
        //  If replacing fragment shader: output count must match
        new_fragment_shader.is_some() ==> {
            new_fragment_shader.unwrap().ghost_interface().outputs.len()
                == old_pipeline.ghost_fragment_shader_interface().outputs.len()
        },
    ensures
        match result {
            Ok(new_pipeline) => {
                //  New pipeline is layout-compatible with old
                new_pipeline.ghost_layout_compatible(old_pipeline)
                //  All existing descriptor sets remain valid
                && forall |ds: &DescriptorSet|
                    ds.ghost_compatible_with_layout(old_pipeline.ghost_layout()) ==>
                        ds.ghost_compatible_with_layout(new_pipeline.ghost_layout())
            }
            Err(_) => true
        }
{
    ...
}
```

The `ghost_layout_compatible` ensures clause is the critical property: it guarantees that after the swap, every descriptor set that was valid for the old pipeline is still valid for the new one. This means the hot-reload can happen between frames without rebinding any descriptor sets — the next frame's draw calls work unchanged.

### 17.3 Atomic Swap Pattern

The hot-reload itself must be atomic with respect to frame rendering — you can't swap a pipeline while a frame is in flight that uses it. The ghost model handles this through the pending submission log (section 6.5):

```rust
pub fn swap_pipeline(
    renderer: &mut Renderer,
    old_pipeline: &Pipeline,
    new_pipeline: Pipeline,
)
    requires
        //  No in-flight frame uses the old pipeline
        renderer.device.ghost_no_pending_pipeline_references(old_pipeline),
        //  New pipeline is layout-compatible (from hot_reload_graphics_pipeline)
        new_pipeline.ghost_layout_compatible(old_pipeline),
    ensures
        renderer.ghost_active_pipeline() == new_pipeline,
        //  Old pipeline can now be destroyed
        renderer.device.ghost_no_pending_references(old_pipeline.ghost_handle),
{
    ...
}
```

This composes with the fence-wait mechanism: wait for in-flight frames to complete, swap the pipeline, record new frames with the new pipeline. Verus proves the swap is safe — no frame sees a half-swapped state.

---

## 18. Testing Strategy

### 18.1 Ghost State Model Validation

The ghost state model is Caldera's specification — if it doesn't accurately reflect Vulkan's actual behavior, verified programs could still have bugs. To validate the model, we compare it against two oracles.

The first oracle is the Vulkan validation layers. For every test case, we run the same command sequence with validation layers enabled and check that Caldera's ghost state model would accept/reject it in agreement with the validation layers. Test cases include both valid sequences (which both should accept) and intentionally invalid sequences (which both should reject). Disagreements indicate a bug in either the ghost model or the validation layers.

The second oracle is the Vulkan specification itself. Each Verus precondition is annotated with the VUID it encodes. A coverage tool checks that the VUID's text semantically matches the precondition's logic. This is a manual review process aided by tooling that extracts VUID text from the spec XML and presents it alongside the Verus precondition for side-by-side comparison.

### 18.2 End-to-End Rendering Tests

Rendering tests produce images and compare them against reference images (golden files). The comparison uses a perceptual metric (SSIM or FLIP) with a tolerance threshold. These tests run on CI with multiple GPU vendors (NVIDIA, AMD, Intel) via software rendering (SwiftShader, lavapipe) and, where available, real hardware.

### 18.3 Adversarial Fuzzing

A fuzzer generates random command sequences and checks that Caldera's ghost model correctly classifies them as valid or invalid (compared against validation layer output). This is particularly valuable for the synchronization model, where the interaction between barriers, render passes, and queue submissions creates a large state space that is hard to cover with hand-written tests.

### 18.4 Verification CI

Verus is run on all proof modules in CI. Verification time budgets are tracked — if a proof takes more than 60 seconds, it's flagged for refactoring (long verification times usually indicate the solver is struggling and the proof needs better hints).

---

## 19. Implementation Roadmap

### Phase 0: Skeleton and Smoke Test (Weeks 1–3)

Establish the crate structure, the `ash` FFI dependency, and the simplest possible verified wrapper: instance creation and device creation with ghost state establishing device capabilities. Verify a trivial program that creates an instance, selects a physical device, and creates a logical device. No rendering, no command buffers — just proving that the infrastructure works.

### Phase 1: Buffers, Commands, and Compute (Weeks 4–8)

Add buffer creation, memory allocation and binding, command pool and command buffer wrappers, and compute pipeline wrappers. Implement the synchronization model for single-queue compute-only workloads (barriers between compute dispatches). Integrate with CuTe-RS via `caldera-bridge` for verified compute dispatch. The deliverable is a verified program that allocates buffers, dispatches a CuTe-RS kernel, barriers, dispatches another kernel, and reads back results.

### Phase 2: Images, Render Passes, and Graphics (Weeks 9–15)

Add image creation and layout tracking, render pass and framebuffer wrappers with the ghost render pass model, graphics pipeline wrappers, descriptor set wrappers, and draw commands. Implement image layout transition verification. The deliverable is a verified program that renders a triangle to an offscreen image, transitions the image, and reads it back. This is the first end-to-end rendering test.

### Phase 3: Swapchain, Presentation, and VR (Weeks 16–22)

Add swapchain management, presentation, and the VR-specific layer (OpenXR integration, stereo rendering, multiview). Implement semaphore-based ghost state threading for cross-submission synchronization (necessary for the swapchain acquire-render-present cycle). The deliverable is a verified VR application that renders stereo frames and presents them via OpenXR.

### Phase 4: CuTe-RS SPIR-V Backend (Weeks 20–26, overlapping with Phase 3)

In parallel with Caldera's VR work, implement CuTe-RS's SPIR-V backend so that compute kernels can be dispatched through Vulkan rather than requiring a separate CUDA or WebGPU runtime. This is the enabling work for running verified compute and verified rendering in the same Vulkan submission.

### Phase 5: Asset Pipeline and Cross-Crate Composition (Weeks 27–33)

Implement the verified asset pipeline (section 13): `VerifiedMesh` trait bridging verus-topology to Caldera, ghost mesh invariants on buffers, draw-time index validation. Implement GPU readback integrity (section 16.3). Thread ghost invariants across crate boundaries end-to-end: verus-topology → verus-geometry → CuTe-RS → Caldera. The deliverable is a verified pipeline from mesh construction to rendered frame with invariants preserved at every boundary.

### Phase 6: Temporal Invariants and Information Flow (Weeks 34–40)

Add temporal loop invariants for the main render loop (section 14): memory stability, ring buffer correctness, animation continuity. Implement ghost taint labels for social VR information flow control (section 15). The deliverable is a verified multiplayer VR application where player privacy is provably maintained and multi-frame stability is proven.

### Phase 7: Hardening, Hot-Reload, and Multi-Queue (Weeks 41–48)

Implement verified hot-reload (section 17). Expand VUID coverage, add multi-queue support (async compute with proper ownership transfer verification), add format feature checking, and harden the synchronization model with adversarial fuzzing. Performance optimization of the runtime (ensure zero overhead vs. raw `ash` calls). Comprehensive documentation and example VR applications.

---

## 20. Key Design Decisions and Alternatives

**Why ash and not vulkano as the base?** `ash` is a thin, zero-overhead FFI binding to the Vulkan C API. It does no validation, no state tracking, and no lifetime management — it's the moral equivalent of `libc` for Vulkan. This is exactly what we want: a minimal trusted base on top of which we build verified safety. Vulkano adds runtime validation, reference counting, and implicit synchronization, all of which would conflict with Caldera's ghost-state approach. We'd be fighting vulkano's runtime checks rather than replacing them with static ones.

**Why not extend wgpu instead?** wgpu provides a safe WebGPU-like API that abstracts over Vulkan, Metal, and DX12. It's excellent for portable applications but fundamentally limits what you can express — it doesn't expose Vulkan's full pipeline barrier model, subpass system, or advanced synchronization. For VR, where you need maximum control over frame timing, async compute, and hardware-specific features, wgpu's abstraction level is too high. Additionally, wgpu's safety is achieved through runtime checks and internal state tracking, not formal verification — you get safety but not proofs.

**Why not verify at the SPIR-V level too?** Verifying shader code at the SPIR-V level is a separate and largely orthogonal problem. CuTe-RS handles verification of compute shader logic (bounds, correctness) at the Rust source level. Verifying graphics shaders (vertex, fragment) would require either a shader DSL in Rust that Verus can analyze (possible but a large project) or a SPIR-V verifier that checks properties after compilation (closer to model checking than deductive verification). This is valuable future work but not in scope for Caldera v0.1. The pragmatic approach is to trust the graphics shaders and verify everything around them — the command recording, synchronization, resource management, and compute kernels.

**Why ghost state rather than type-state?** A type-state approach (encoding resource state in the Rust type system, e.g., `Image<LayoutColorAttachment>` vs. `Image<LayoutShaderReadOnly>`) was considered. It has the advantage of not requiring Verus — the Rust compiler enforces the state transitions. But it has severe ergonomic problems: every barrier would change the type of every affected resource, requiring either rebinding or extensive use of generics. It also can't express quantified properties ("all images in this descriptor set are in the correct layout") and doesn't scale to the synchronization model (which requires reasoning about happens-before relationships, not just current state). Ghost state with Verus is more expressive and more ergonomic, at the cost of requiring an external verification tool.

**Why track sync state per-resource rather than globally?** A global synchronization model (tracking all resources' states in a single ghost object) would simplify the API but create verification scaling problems — every command would need to reason about the entire global state. Per-resource tracking with a ghost `Map` in the command buffer builder keeps the verification modular: a barrier on image A only affects image A's ghost state, and the verifier doesn't need to consider image B.

---

## 21. Risks and Mitigations

**Risk: The Verus ghost state model becomes unwieldy.** The command buffer builder's ghost state is large (current render pass, bound pipeline, bound descriptor sets, dynamic state, per-resource sync state). If verification times become unacceptable, it may be necessary to split the ghost state into smaller pieces that are verified independently. Mitigation: use Verus's modular verification (verify each function independently against its spec), keep quantifiers bounded, and use intermediate lemmas aggressively.

**Risk: The synchronization model is too conservative.** If the ghost model rejects valid programs that are actually correct, users will fight the verifier rather than work with it. Mitigation: validate the model against real VR rendering code early (not just toy examples), and design the model to be tightenable over time (start permissive, add restrictions as we discover what's necessary).

**Risk: Driver divergence from spec.** Different GPU vendors interpret ambiguous parts of the Vulkan spec differently. A program that is valid per Caldera's model might still exhibit driver-specific bugs. Mitigation: test on multiple vendors' drivers (NVIDIA, AMD, Intel, SwiftShader), and document known vendor divergences.

**Risk: The API is too verbose.** If every Vulkan call requires explicitly threading ghost state, the API will be painful to use. Mitigation: use Verus's support for automatically threading ghost state through `&mut self` receivers, provide helper macros for common patterns (barrier declarations, render pass setup), and invest heavily in error messages (a Verus precondition failure should tell the user "you forgot a barrier between the compute write and the vertex read," not "precondition on line 847 of sync_model.rs failed").

---

## 22. Open Questions

How should we handle Vulkan extensions? Extensions add new commands, new validity rules, and new resource types. The ghost model needs to be extensible without modifying the core types. A trait-based extension mechanism (where extensions provide ghost state additions and precondition additions) is the likely approach, but the design needs more thought.

How should we model descriptor indexing and bindless resources? Modern Vulkan uses `VK_EXT_descriptor_indexing` for large descriptor arrays indexed by shader-computed values. The ghost model can't track which descriptor is accessed at each draw call because the index is computed on the GPU. The pragmatic approach is to require that all descriptors in a bindless array are valid and in the correct state (a strong but simple invariant).

How should we handle timeline semaphores? Timeline semaphores (`VK_KHR_timeline_semaphore`) use monotonically increasing counter values instead of binary signaled/unsignaled state. The ghost model needs to track the counter value and verify that wait values are less than or equal to signal values. This is straightforward but adds complexity to the semaphore ghost state.

~~Should Caldera support Vulkan 1.0/1.1, or target 1.3+ only?~~ **Decided: Vulkan 1.3+ only.** Dynamic rendering (`VK_KHR_dynamic_rendering`, core in 1.3) eliminates the `VkRenderPass`/`VkFramebuffer` ghost model complexity. Synchronization2 (`VK_KHR_synchronization2`, core in 1.3) provides the cleaner `VkPipelineStageFlags2`/`VkAccessFlags2` types that the sync model is designed around. All VR headsets with Vulkan support have 1.3. The legacy render pass model is available for multi-subpass use cases but is not the primary path.

How should we handle GPU memory aliasing? Vulkan allows multiple resources to be bound to overlapping regions of the same device memory. Aliased resources have additional validity rules (you must not access two aliased resources in the same submission unless they're in the same render pass and one is an attachment). The ghost model would need to track aliasing relationships, which adds complexity. For v0.1, disallowing aliasing (or treating it as unverified) is reasonable.

---

This document is a companion to the CuTe-RS design document and will evolve alongside it. The two projects share a verification philosophy, a toolchain, and a workspace, and their design decisions should be considered jointly.
