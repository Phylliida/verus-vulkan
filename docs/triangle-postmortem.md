# Triangle Demo Postmortem — Error Catalog

Every error encountered while building the verified-FFI triangle demo, categorized by
whether it's a **library bug** (we should fix in verus-vulkan) or an **integration issue**
(caller mistake, but the library could prevent or improve diagnostics).

---

## Library Bugs (must fix)

### 1. Missing clear values in `raw_cmd_begin_render_pass`

**Symptom**: Screen was gray/undefined color despite CLEAR load op.

**Root cause**: `raw_cmd_begin_render_pass` built a `RenderPassBeginInfo` without calling
`.clear_values(...)`. When the render pass uses `VK_ATTACHMENT_LOAD_OP_CLEAR`, Vulkan
requires `pClearValues` to contain a valid entry for each attachment. Without it, the
behavior is undefined (in practice: uninitialized memory as clear color).

**Fix applied**: Added hardcoded `[0.1, 0.1, 0.1, 1.0]` clear value.

**Proper fix**: `raw_cmd_begin_render_pass` should accept clear color parameters. The
verified wrapper `vk_cmd_begin_render_pass` should pass them through. Suggested signature:

```rust
fn raw_cmd_begin_render_pass(
    ctx: &VulkanContext, cb: u64, rp: u64, fb: u64, w: u32, h: u32,
    clear_r: f32, clear_g: f32, clear_b: f32, clear_a: f32,
)
```

Or better: take a `&[vk::ClearValue]` slice for multi-attachment render passes.

---

### 2. `vk_acquire_next_image` required caller-specified index

**Symptom**: Compile-time API mismatch — no way to let Vulkan choose the swapchain image.

**Root cause**: The original `vk_acquire_next_image` took `idx: u64` as input (the caller
specifies which image to acquire). In Vulkan, `vkAcquireNextImageKHR` _returns_ the
index — the driver chooses it. The API was backwards.

**Fix applied**: Added `vk_acquire_next_image_any` that returns the driver-chosen index.

**Proper fix**: The original `vk_acquire_next_image` should be renamed/removed. The standard
API should always return the index. The ghost postcondition should ensure the returned
index is in bounds: `ensures idx < sc@.image_states.len()`.

---

### 3. `pub(crate)` visibility on command recording FFI functions

**Symptom**: Binary couldn't call `vk_begin_command_buffer`, `vk_cmd_draw`, etc.

**Root cause**: 8 command recording functions were `pub(crate)` instead of `pub`. Since
the triangle binary is a separate crate target, it couldn't access them.

**Functions affected**: `vk_begin_command_buffer`, `vk_end_command_buffer`,
`vk_cmd_begin_render_pass`, `vk_cmd_end_render_pass`, `vk_cmd_draw`,
`vk_cmd_bind_pipeline`, `ffi_cmd_set_viewport`, `ffi_cmd_set_scissor`.

**Proper fix**: All FFI functions in `ffi.rs` should be `pub`. They're the public API
of the crate. Audit all functions and ensure consistent visibility.

---

### 4. Graphics pipeline creation was a non-functional stub

**Symptom**: Pipeline creation produced a pipeline with no shader stages.

**Root cause**: `raw_create_graphics_pipeline(ctx, layout, rp)` took only layout and
render pass handles — no shader modules. It created a pipeline with zero shader stages,
no vertex input, no rasterization state. This is not a valid Vulkan pipeline.

**Fix applied**: Replaced with full version taking vert/frag shader handles and complete
pipeline state (input assembly, rasterization, blend, dynamic viewport/scissor).

**Proper fix**: Never merge stub implementations of raw Vulkan functions. If the full
implementation isn't ready, mark it `unimplemented!()` or `todo!()` so it fails loudly.

---

### 5. No macOS portability support in `VulkanContext`

**Symptom**: `ERROR_INCOMPATIBLE_DRIVER` on macOS with MoltenVK.

**Root cause**: MoltenVK is a "portability driver" — it requires:
- `VK_KHR_portability_enumeration` instance extension
- `VK_INSTANCE_CREATE_ENUMERATE_PORTABILITY_KHR` flag
- `VK_KHR_portability_subset` device extension

Without these, the Vulkan loader won't enumerate MoltenVK as an ICD.

**Fix applied**: Added `#[cfg(target_os = "macos")]` blocks to `VulkanContext::new()` for
the instance extension/flag. Device extension is caller-provided.

**Proper fix**: `VulkanContext::new()` should auto-detect portability requirements:
1. Always add portability enumeration on macOS
2. Auto-add `VK_KHR_portability_subset` to device extensions on macOS
3. Document that callers on macOS don't need to worry about portability

---

### 6. No validation layer fallback in `VulkanContext`

**Symptom**: `ERROR_LAYER_NOT_PRESENT` panic when validation layers aren't installed.

**Root cause**: `create_instance` was called with validation layer name but no error
handling for missing layers. Most developer machines don't have validation layers
installed by default.

**Fix applied**: Added match on `ERROR_LAYER_NOT_PRESENT` to retry without layers.

**Proper fix**: Keep the fallback. Also consider:
- Log which layers were requested vs. available
- Query `vkEnumerateInstanceLayerProperties` first to check availability
- Make `enable_validation` a best-effort flag, not a requirement

---

### 7. No resource destruction helpers / crash on close

**Symptom**: "Rust cannot catch foreign exceptions" crash when closing window.

**Root cause**: `VkState::destroy()` only called `device_wait_idle` + `destroy_surface` +
`ctx.destroy()` but didn't destroy any intermediate objects (pipeline, framebuffers,
image views, render pass, command pool, sync objects, swapchain). MoltenVK threw an
Objective-C exception when destroying the device with live children.

**Proper fix**: The library should provide a `vk_destroy_*` FFI function for every
`vk_create_*` function. Currently missing raw destroy wrappers for some objects.
Consider adding a `VkState::destroy_all()` or at minimum documenting the required
destruction order.

---

## Integration Issues (library could help prevent)

### 8. Wrong function argument count/order

**Symptom**: Compile errors calling `vk_create_device` with 3 args (has 2),
`vk_get_device_queue` with wrong ghost param position.

**Root cause**: FFI function signatures aren't obvious — ghost params can be anywhere,
and different functions have different conventions.

**Library improvement**: Establish and document a consistent convention:
- Ghost params always come LAST (after all exec params)
- Group related params together (e.g., all semaphore handles together)
- Add doc comments to every FFI function showing usage example

---

### 9. `vk_queue_submit` / `vk_queue_present_khr` casting confusion

**Symptom**: Type mismatches between `u64` and `u32` for image indices, pipeline stages.

**Root cause**: The FFI uses `u64` for handles but Vulkan uses `u32` for indices and
enum values. The conversions (`as u32`, `.as_raw() as u32`) are error-prone.

**Library improvement**: Consider type aliases or newtypes:
```rust
type VkHandle = u64;
type ImageIndex = u32;
type VkFormat = u32;
```

Or better: accept ash types directly in the raw functions and only convert at the
boundary, so callers don't need to know about `.as_raw()`.

---

### 10. render pass load_op/store_op use raw integers with non-obvious mapping

**Symptom**: Had to verify manually that `AttachmentLoadOp::CLEAR.as_raw()` maps to 1,
which maps to the `if load_op == 1 { CLEAR }` branch in `raw_create_render_pass`.

**Root cause**: The raw function maps integers to enums with `if/else` chains instead of
using ash's `from_raw()`.

**Library improvement**: Accept `u32` and use `vk::AttachmentLoadOp::from_raw(load_op as i32)`
directly, eliminating the manual mapping. Or accept ash enum types.

---

### 11. No `request_redraw()` after window creation (winit issue, not vulkan)

**Symptom**: Render function never called — screen showed default window background.

**Root cause**: winit 0.30's `ApplicationHandler` doesn't auto-fire `RedrawRequested`
after `resumed()`. The application must explicitly call `window.request_redraw()`.

**Library improvement**: Not a verus-vulkan issue, but if we provide a frame loop helper
or example, it should include this call.

---

## Summary of Required Library Changes

| Priority | Change | Files | Status |
|----------|--------|-------|--------|
| P0 | Add clear values param to `raw_cmd_begin_render_pass` | ffi.rs | DONE |
| P0 | Fix `vk_acquire_next_image` to return driver-chosen index | ffi.rs | DONE |
| P0 | Make all FFI functions `pub` (audit for `pub(crate)`) | ffi.rs | DONE (89 functions) |
| P1 | Auto-add macOS portability in `VulkanContext` | vk_context.rs | DONE (instance + device) |
| P1 | Add validation layer fallback | vk_context.rs | DONE |
| P1 | Add missing `vk_destroy_*` functions | ffi.rs | DONE |
| P2 | Remove/replace pipeline creation stub | ffi.rs | DONE |
| P2 | Document ghost param convention (always last) | ffi.rs | DONE |
| P2 | Replace raw int enums with `from_raw()` conversions | ffi.rs | DONE |
| P2 | Add type aliases for handles vs indices vs enums | ffi.rs | DONE |
| P2 | Pass clear color through `cmd_begin_render_pass_exec` | runtime/command_buffer.rs | DONE |
