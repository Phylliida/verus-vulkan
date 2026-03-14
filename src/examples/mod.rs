//! # Verified Vulkan Usage Examples
//!
//! Each module is a self-contained proof showing a common Vulkan workflow.
//! Run them with:
//!
//! ```bash
//! # Single example
//! cargo-verus verify --module examples::render_triangle
//!
//! # Or verify everything (includes all examples)
//! cargo-verus verify
//! ```
//!
//! These are pure proof modules — no exec code. Verus checks that every
//! `proof fn` satisfies its `ensures` clause, giving you a verified
//! walkthrough of the Vulkan state machine.

pub mod render_triangle;
pub mod ray_traced_sphere;
pub mod shading_rate_setup;
pub mod nested_command_buffer_lifecycle;
