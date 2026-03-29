use vstd::prelude::*;
use crate::resource::*;
use crate::recording::*;
use crate::recording_commands::*;
use crate::render_pass::*;
use crate::sync::*;

verus! {

//  ── Types ───────────────────────────────────────────────────────────────

///  Ghost assumptions recorded at secondary command buffer recording time.
///
///  When a secondary command buffer is recorded, it captures assumptions
///  about the primary command buffer's state at execution time. These
///  assumptions must be verified when cmd_execute_commands is called.
pub struct SecondaryAssumptions {
    ///  Whether the secondary CB requires being inside a render pass.
    pub requires_render_pass: bool,
    ///  Expected render pass id, if inside a render pass.
    pub expected_render_pass_id: Option<nat>,
    ///  Expected subpass index, if inside a render pass.
    pub expected_subpass_index: Option<nat>,
    ///  Expected bound graphics pipeline, if any.
    pub expected_graphics_pipeline: Option<nat>,
    ///  Expected color attachment formats (if inside render pass).
    pub expected_color_formats: Option<Seq<nat>>,
    ///  Expected depth attachment format (if inside render pass).
    pub expected_depth_format: Option<nat>,
    ///  Set of resources the secondary CB will access.
    pub referenced_resources: Set<ResourceId>,
    ///  Barrier entries the secondary CB records.
    pub barrier_entries: Seq<BarrierEntry>,
}

///  Ghost state for a recorded secondary command buffer.
pub struct SecondaryCommandBuffer {
    ///  The assumptions made during recording.
    pub assumptions: SecondaryAssumptions,
    ///  The commands recorded in the secondary CB.
    pub command_log: Seq<RecordedCommand>,
    ///  Whether the secondary CB is in Executable state.
    pub executable: bool,
}

//  ── Spec Functions ──────────────────────────────────────────────────────

///  The primary's state satisfies the secondary CB's assumptions.
///  `rp` is the render pass state, needed for format checking.
pub open spec fn assumptions_satisfied(
    assumptions: SecondaryAssumptions,
    primary_ctx: RecordingContext,
    rp: RenderPassState,
) -> bool {
    //  If secondary requires render pass, primary must be in one
    (assumptions.requires_render_pass ==> in_render_pass(primary_ctx.state))

    //  If secondary expects specific render pass, primary must match
    && (match assumptions.expected_render_pass_id {
        Some(rp_id) => primary_ctx.state.active_render_pass.is_some()
            && primary_ctx.state.active_render_pass.unwrap().render_pass_id == rp_id,
        None => true,
    })

    //  If secondary expects specific subpass, primary must match
    && (match assumptions.expected_subpass_index {
        Some(sp_idx) => primary_ctx.state.active_render_pass.is_some()
            && primary_ctx.state.active_render_pass.unwrap().subpass_index == sp_idx,
        None => true,
    })

    //  If secondary expects bound pipeline, primary must have it
    && (match assumptions.expected_graphics_pipeline {
        Some(pipeline_id) =>
            primary_ctx.state.bound_graphics_pipeline == Some(pipeline_id),
        None => true,
    })

    //  Color attachment formats must match
    && (match assumptions.expected_color_formats {
        Some(formats) => primary_ctx.state.active_render_pass.is_some()
            && ({
                let sp_idx = primary_ctx.state.active_render_pass.unwrap().subpass_index;
                sp_idx < rp.subpasses.len()
                && rp.subpasses[sp_idx as int].color_attachments.len() == formats.len()
                && forall|i: int| #![trigger formats[i]]
                    0 <= i < formats.len() ==> {
                    let att_idx = rp.subpasses[sp_idx as int].color_attachments[i].attachment_index;
                    att_idx < rp.attachments.len()
                    && rp.attachments[att_idx as int].format == formats[i]
                }
            }),
        None => true,
    })

    //  Depth format must match
    && (match assumptions.expected_depth_format {
        Some(fmt) => primary_ctx.state.active_render_pass.is_some()
            && ({
                let sp_idx = primary_ctx.state.active_render_pass.unwrap().subpass_index;
                sp_idx < rp.subpasses.len()
                && rp.subpasses[sp_idx as int].depth_attachment.is_some()
                && ({
                    let att_idx = rp.subpasses[sp_idx as int].depth_attachment.unwrap().attachment_index;
                    att_idx < rp.attachments.len()
                    && rp.attachments[att_idx as int].format == fmt
                })
            }),
        None => true,
    })
}

///  Ghost update: execute a secondary CB within a primary's recording context.
///
///  This merges the secondary's resources and barrier log into the primary.
///  The recording state is unchanged (secondary CBs don't change primary state
///  in Vulkan — only the primary's inherited state matters).
pub open spec fn execute_secondary(
    primary_ctx: RecordingContext,
    secondary: SecondaryCommandBuffer,
) -> RecordingContext {
    RecordingContext {
        //  State unchanged (secondary inherits primary's state)
        state: primary_ctx.state,
        //  Resources accumulated
        referenced_resources:
            primary_ctx.referenced_resources.union(secondary.assumptions.referenced_resources),
        //  Commands accumulated
        command_log: primary_ctx.command_log + secondary.command_log,
        //  Barriers accumulated
        barrier_log: primary_ctx.barrier_log + secondary.assumptions.barrier_entries,
    }
}

///  A secondary command buffer is well-formed.
pub open spec fn secondary_well_formed(secondary: SecondaryCommandBuffer) -> bool {
    secondary.executable
}

///  No assumptions: a secondary CB that doesn't require any specific state.
pub open spec fn no_assumptions() -> SecondaryAssumptions {
    SecondaryAssumptions {
        requires_render_pass: false,
        expected_render_pass_id: None,
        expected_subpass_index: None,
        expected_graphics_pipeline: None,
        expected_color_formats: None,
        expected_depth_format: None,
        referenced_resources: Set::empty(),
        barrier_entries: Seq::empty(),
    }
}

///  Executing N secondary command buffers sequentially.
pub open spec fn execute_n_secondaries(
    primary_ctx: RecordingContext,
    secondaries: Seq<SecondaryCommandBuffer>,
) -> RecordingContext
    decreases secondaries.len(),
{
    if secondaries.len() == 0 {
        primary_ctx
    } else {
        execute_secondary(
            execute_n_secondaries(primary_ctx, secondaries.drop_last()),
            secondaries.last(),
        )
    }
}

//  ── Proofs ──────────────────────────────────────────────────────────────

///  If assumptions are satisfied, it is safe to execute the secondary CB.
///  (This is the core soundness property of secondary command buffers.)
pub proof fn lemma_satisfied_assumptions_enable_execute(
    assumptions: SecondaryAssumptions,
    primary_ctx: RecordingContext,
    rp: RenderPassState,
)
    requires
        assumptions_satisfied(assumptions, primary_ctx, rp),
        assumptions.requires_render_pass,
    ensures
        in_render_pass(primary_ctx.state),
{
}

///  Executing a secondary CB accumulates its resources.
pub proof fn lemma_execute_accumulates_resources(
    primary_ctx: RecordingContext,
    secondary: SecondaryCommandBuffer,
    r: ResourceId,
)
    requires
        secondary.assumptions.referenced_resources.contains(r),
    ensures
        execute_secondary(primary_ctx, secondary)
            .referenced_resources.contains(r),
{
}

///  Executing a secondary CB preserves the primary's existing resources.
pub proof fn lemma_execute_preserves_primary_resources(
    primary_ctx: RecordingContext,
    secondary: SecondaryCommandBuffer,
    r: ResourceId,
)
    requires
        primary_ctx.referenced_resources.contains(r),
    ensures
        execute_secondary(primary_ctx, secondary)
            .referenced_resources.contains(r),
{
}

///  Executing a secondary CB does not change the primary's recording state.
pub proof fn lemma_execute_preserves_state(
    primary_ctx: RecordingContext,
    secondary: SecondaryCommandBuffer,
)
    ensures
        execute_secondary(primary_ctx, secondary).state == primary_ctx.state,
{
}

///  A secondary CB with no assumptions is always satisfied.
pub proof fn lemma_no_assumptions_always_satisfied(
    primary_ctx: RecordingContext,
    rp: RenderPassState,
)
    ensures
        assumptions_satisfied(no_assumptions(), primary_ctx, rp),
{
}

///  Executing a secondary with no resources and no barriers is identity-like.
pub proof fn lemma_execute_empty_secondary_preserves_resources(
    primary_ctx: RecordingContext,
)
    ensures ({
        let empty_secondary = SecondaryCommandBuffer {
            assumptions: no_assumptions(),
            command_log: Seq::empty(),
            executable: true,
        };
        execute_secondary(primary_ctx, empty_secondary).referenced_resources
            == primary_ctx.referenced_resources
    }),
{
    //  referenced_resources.union(Set::empty()) == referenced_resources
    let empty_secondary = SecondaryCommandBuffer {
        assumptions: no_assumptions(),
        command_log: Seq::empty(),
        executable: true,
    };
    let result = execute_secondary(primary_ctx, empty_secondary);
    assert(result.referenced_resources =~= primary_ctx.referenced_resources);
}

///  Executing secondaries in sequence is associative with resource accumulation.
pub proof fn lemma_execute_n_accumulates_all_resources(
    primary_ctx: RecordingContext,
    secondaries: Seq<SecondaryCommandBuffer>,
    k: nat,
    r: ResourceId,
)
    requires
        k < secondaries.len(),
        secondaries[k as int].assumptions.referenced_resources.contains(r),
    ensures
        execute_n_secondaries(primary_ctx, secondaries)
            .referenced_resources.contains(r),
    decreases secondaries.len(),
{
    if secondaries.len() > 0 {
        let prefix = secondaries.drop_last();
        let last = secondaries.last();
        if k == secondaries.len() - 1 {
            //  r is in the last secondary's resources
            lemma_execute_accumulates_resources(
                execute_n_secondaries(primary_ctx, prefix),
                last,
                r,
            );
        } else {
            //  r is in a prefix secondary — recurse
            assert(k < prefix.len());
            assert(prefix[k as int] == secondaries[k as int]);
            lemma_execute_n_accumulates_all_resources(primary_ctx, prefix, k, r);
            //  Now r is in execute_n_secondaries(primary_ctx, prefix).referenced_resources
            lemma_execute_preserves_primary_resources(
                execute_n_secondaries(primary_ctx, prefix),
                last,
                r,
            );
        }
    }
}

///  Mismatched color formats cause assumptions_satisfied to return false.
pub proof fn lemma_format_mismatch_not_satisfied(
    assumptions: SecondaryAssumptions,
    primary_ctx: RecordingContext,
    rp: RenderPassState,
)
    requires
        assumptions.expected_color_formats.is_some(),
        assumptions_satisfied(assumptions, primary_ctx, rp),
        primary_ctx.state.active_render_pass.is_some(),
    ensures ({
        let sp_idx = primary_ctx.state.active_render_pass.unwrap().subpass_index;
        sp_idx < rp.subpasses.len()
        && rp.subpasses[sp_idx as int].color_attachments.len()
            == assumptions.expected_color_formats.unwrap().len()
    }),
{
}

///  Assumptions with a specific render pass are stricter than no-assumption.
pub proof fn lemma_render_pass_assumption_implies_in_render_pass(
    assumptions: SecondaryAssumptions,
    primary_ctx: RecordingContext,
    rp: RenderPassState,
)
    requires
        assumptions_satisfied(assumptions, primary_ctx, rp),
        assumptions.expected_render_pass_id.is_some(),
    ensures
        primary_ctx.state.active_render_pass.is_some(),
        primary_ctx.state.active_render_pass.unwrap().render_pass_id
            == assumptions.expected_render_pass_id.unwrap(),
{
}

} //  verus!
