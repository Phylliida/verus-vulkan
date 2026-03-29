//! # Example: Nested Command Buffer Lifecycle
//!
//! Models using VK_EXT_nested_command_buffer for multi-level secondary CB execution:
//!   1. Create initial nesting state from device limits
//!   2. Nest one level (execute a secondary command buffer)
//!   3. Nest another level (secondary within secondary)
//!   4. Unnest back to level 1
//!   5. Unnest back to level 0
//!   6. Prove depth is always bounded
//!
//! Uses the checked variants to demonstrate compile-time safety.

use vstd::prelude::*;
use crate::nested_command_buffers::*;

verus! {

//  ── Device Configuration ────────────────────────────────────────────────

///  Device supports up to 3 levels of nesting with render pass inheritance.
pub open spec fn device_limits() -> NestedCommandBufferLimits {
    NestedCommandBufferLimits {
        max_command_buffer_nesting_level: 3,
        supports_render_pass_inheritance: true,
    }
}

//  ── Step-by-step Proofs ─────────────────────────────────────────────────

///  Step 1: Create initial state — level 0, not isolated.
pub proof fn step1_initial_state()
    ensures ({
        let s = initial_nesting_state(device_limits());
        nesting_depth(s) == 0
        && !s.state_isolated
        && nested_cb_well_formed(s, device_limits())
    }),
{
    lemma_initial_well_formed(device_limits());
    lemma_initial_level_zero(device_limits());
    lemma_initial_not_isolated(device_limits());
}

///  Step 2: Nest to level 1 (execute a secondary command buffer).
///  Uses the checked variant — requires proof of can_nest_deeper.
pub proof fn step2_nest_to_level_1()
    ensures ({
        let s0 = initial_nesting_state(device_limits());
        let s1 = nest_command_buffer_checked(s0, device_limits());
        nesting_depth(s1) == 1
        && s1.state_isolated  //  secondary CB state is isolated
        && nested_cb_well_formed(s1, device_limits())
    }),
{
    let s0 = initial_nesting_state(device_limits());
    lemma_initial_well_formed(device_limits());
    lemma_checked_nest_safe(s0, device_limits());
}

///  Step 3: Nest to level 2 (secondary within secondary).
pub proof fn step3_nest_to_level_2()
    ensures ({
        let s0 = initial_nesting_state(device_limits());
        let s1 = nest_command_buffer_checked(s0, device_limits());
        let s2 = nest_command_buffer_checked(s1, device_limits());
        nesting_depth(s2) == 2
        && nested_cb_well_formed(s2, device_limits())
    }),
{
    let s0 = initial_nesting_state(device_limits());
    lemma_initial_well_formed(device_limits());
    lemma_checked_nest_safe(s0, device_limits());

    let s1 = nest_command_buffer_checked(s0, device_limits());
    lemma_checked_nest_safe(s1, device_limits());
}

///  Step 4: Unnest from level 2 back to level 1.
pub proof fn step4_unnest_to_level_1()
    ensures ({
        let s0 = initial_nesting_state(device_limits());
        let s1 = nest_command_buffer(s0);
        let s2 = nest_command_buffer(s1);
        let s3 = unnest_command_buffer_checked(s2, device_limits());
        nesting_depth(s3) == 1
        && !s3.state_isolated  //  back to parent scope
        && nested_cb_well_formed(s3, device_limits())
    }),
{
    let s0 = initial_nesting_state(device_limits());
    lemma_initial_well_formed(device_limits());
    lemma_can_nest_implies_well_formed_after(s0, device_limits());

    let s1 = nest_command_buffer(s0);
    lemma_can_nest_implies_well_formed_after(s1, device_limits());

    let s2 = nest_command_buffer(s1);
    lemma_checked_unnest_safe(s2, device_limits());
}

///  Step 5: Full roundtrip — nest twice, unnest twice, back to level 0.
pub proof fn step5_full_roundtrip()
    ensures ({
        let s0 = initial_nesting_state(device_limits());
        let s1 = nest_command_buffer(s0);
        let s2 = nest_command_buffer(s1);
        let s3 = unnest_command_buffer(s2);
        let s4 = unnest_command_buffer(s3);
        nesting_depth(s4) == 0
        && nested_cb_well_formed(s4, device_limits())
    }),
{
    let s0 = initial_nesting_state(device_limits());
    lemma_initial_well_formed(device_limits());
    lemma_can_nest_implies_well_formed_after(s0, device_limits());
    let s1 = nest_command_buffer(s0);
    lemma_can_nest_implies_well_formed_after(s1, device_limits());
    let s2 = nest_command_buffer(s1);
    lemma_unnest_preserves_well_formed(s2, device_limits());
    let s3 = unnest_command_buffer(s2);
    lemma_unnest_preserves_well_formed(s3, device_limits());
}

///  Step 6: Nest 3 times hits the limit — can't nest further.
pub proof fn step6_max_depth_reached()
    ensures ({
        let s0 = initial_nesting_state(device_limits());
        let s1 = nest_command_buffer(s0);
        let s2 = nest_command_buffer(s1);
        let s3 = nest_command_buffer(s2);
        nesting_depth(s3) == 3
        && nested_cb_well_formed(s3, device_limits())
        && !can_nest_deeper(s3, device_limits())  //  at the limit!
    }),
{
    let s0 = initial_nesting_state(device_limits());
    lemma_initial_well_formed(device_limits());
    lemma_can_nest_implies_well_formed_after(s0, device_limits());
    let s1 = nest_command_buffer(s0);
    lemma_can_nest_implies_well_formed_after(s1, device_limits());
    let s2 = nest_command_buffer(s1);
    lemma_can_nest_implies_well_formed_after(s2, device_limits());
}

///  Step 7: Parent render pass is preserved through nesting.
pub proof fn step7_render_pass_preserved()
    ensures ({
        let s0 = NestedCommandBufferState {
            nesting_level: 0,
            max_nesting_level: 3,
            state_isolated: false,
            parent_render_pass: Some(7),  //  render pass 7 is active
        };
        let s1 = nest_command_buffer(s0);
        s1.parent_render_pass == Some(7nat)  //  preserved!
        && s1.state_isolated  //  but state is isolated
    }),
{
    let s0 = NestedCommandBufferState {
        nesting_level: 0,
        max_nesting_level: 3,
        state_isolated: false,
        parent_render_pass: Some(7),
    };
    lemma_nested_preserves_parent(s0);
    lemma_nest_isolates_state(s0);
}

///  Step 8: Render pass inheritance validation.
pub proof fn step8_render_pass_inheritance()
    ensures ({
        let s = NestedCommandBufferState {
            nesting_level: 1,
            max_nesting_level: 3,
            state_isolated: true,
            parent_render_pass: Some(7),
        };
        //  Device supports inheritance, so nesting inside a render pass is valid
        nested_render_pass_valid(s, device_limits())
    }),
{
}

} //  verus!
