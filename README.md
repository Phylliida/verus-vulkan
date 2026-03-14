# verus-vulkan

Formally verified Rust+Verus Vulkan primitives.

## Prerequisites

- [Verus](https://github.com/verus-lang/verus) built locally (this repo expects it at `../verus/`)

## Verification

Verify the entire crate:

```bash
cd verus-vulkan
../verus/source/target/release/cargo-verus verify
```

Verify a single module (much faster for iteration):

```bash
../verus/source/target/release/cargo-verus verify --module examples::render_triangle
```

Or use a file path:

```bash
../verus/source/target/release/cargo-verus verify --module src/examples/render_triangle.rs
```

## Examples

The `src/examples/` directory contains self-contained proof modules showing common Vulkan workflows. Each example is a series of `proof fn` steps that Verus verifies automatically.

| Example | Description |
|---------|-------------|
| [`render_triangle.rs`](src/examples/render_triangle.rs) | Hello triangle: create render pass, bind pipeline, set dynamic state, draw |
| [`ray_traced_sphere.rs`](src/examples/ray_traced_sphere.rs) | Build BLAS/TLAS for a sphere, create RT pipeline, direct + indirect trace rays |
| [`shading_rate_setup.rs`](src/examples/shading_rate_setup.rs) | Configure fragment shading rate, prove coverage, combiner ops, depth clamp interop |
| [`nested_command_buffer_lifecycle.rs`](src/examples/nested_command_buffer_lifecycle.rs) | Nest/unnest command buffers, prove bounded depth, render pass inheritance |

Run a single example:

```bash
../verus/source/target/release/cargo-verus verify --module examples::render_triangle
```

Run all four examples:

```bash
for ex in render_triangle ray_traced_sphere shading_rate_setup nested_command_buffer_lifecycle; do
  ../verus/source/target/release/cargo-verus verify --module "examples::$ex"
done
```

Or verify the entire crate (includes all examples):

```bash
../verus/source/target/release/cargo-verus verify
```

## Structure

- `src/` — Spec and proof modules modeling Vulkan API state machines
- `src/examples/` — Verified usage examples (good starting point)
- `src/runtime/` — Exec (runtime) implementations with ghost state
