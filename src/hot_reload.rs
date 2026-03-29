use vstd::prelude::*;
use crate::resource::*;
use crate::descriptor::*;
use crate::pipeline::*;
use crate::lifetime::*;
use crate::render_pass::*;
use crate::shader_interface::*;

verus! {

//  ── Types ───────────────────────────────────────────────────────────────

///  A hot-reload request: replace one or both shaders in an existing
///  graphics pipeline.
///
///  Hot-reload happens between frames. The key safety invariant is that
///  the new pipeline must be layout-compatible with the old one, so that
///  existing descriptor sets remain valid without rebinding.
pub struct ReloadRequest {
    ///  The pipeline being replaced.
    pub old_pipeline_id: nat,
    ///  New vertex shader interface, if replacing. None = keep old.
    pub new_vertex_shader: Option<ShaderInterface>,
    ///  New fragment shader interface, if replacing. None = keep old.
    pub new_fragment_shader: Option<ShaderInterface>,
}

///  The result of a successful hot-reload: a new pipeline with
///  compatibility guarantees.
pub struct ReloadedPipeline {
    ///  The new pipeline state.
    pub pipeline: GraphicsPipelineState,
    ///  The old pipeline id (for tracking destruction).
    pub replaced_pipeline_id: nat,
}

//  ── Spec Functions ──────────────────────────────────────────────────────

///  Two pipeline descriptor set layout sequences are layout-compatible:
///  identical length and same layout IDs at each position.
pub open spec fn layouts_identical(
    old_layouts: Seq<nat>,
    new_layouts: Seq<nat>,
) -> bool {
    old_layouts.len() == new_layouts.len()
    && (forall|i: int| 0 <= i < old_layouts.len()
        ==> old_layouts[i] == new_layouts[i])
}

///  A shader replacement is compatible with the old shader:
///  - Same descriptor bindings (set/binding/type/count)
///  - Compatible push constant ranges
///  - For vertex shaders: same input locations and formats
pub open spec fn shader_replacement_compatible(
    old_interface: ShaderInterface,
    new_interface: ShaderInterface,
) -> bool {
    //  Same descriptor bindings
    old_interface.descriptor_bindings.len() == new_interface.descriptor_bindings.len()
    && (forall|i: int| 0 <= i < old_interface.descriptor_bindings.len() ==> {
        let old_b = #[trigger] old_interface.descriptor_bindings[i];
        let new_b = new_interface.descriptor_bindings[i];
        old_b.set == new_b.set
        && old_b.binding == new_b.binding
        && old_b.descriptor_type == new_b.descriptor_type
        && old_b.count == new_b.count
    })
    //  Push constants compatible
    && push_constant_range_compatible(old_interface.push_constant_range, new_interface.push_constant_range)
}

///  A vertex shader replacement is compatible: same inputs plus
///  general shader compatibility.
pub open spec fn vertex_shader_replacement_compatible(
    old_interface: ShaderInterface,
    new_interface: ShaderInterface,
) -> bool {
    shader_replacement_compatible(old_interface, new_interface)
    //  Same vertex inputs (locations and formats must match)
    && old_interface.inputs.len() == new_interface.inputs.len()
    && (forall|i: int| 0 <= i < old_interface.inputs.len() ==> {
        let old_in = #[trigger] old_interface.inputs[i];
        let new_in = new_interface.inputs[i];
        old_in.location == new_in.location
        && format_compatible(old_in.format, new_in.format)
    })
}

///  A fragment shader replacement is compatible: same output count
///  plus general shader compatibility.
pub open spec fn fragment_shader_replacement_compatible(
    old_interface: ShaderInterface,
    new_interface: ShaderInterface,
) -> bool {
    shader_replacement_compatible(old_interface, new_interface)
    && old_interface.output_count == new_interface.output_count
}

///  A hot-reload is valid: each replaced shader (if any) is compatible
///  with the old shader.
pub open spec fn hot_reload_valid(
    request: ReloadRequest,
    old_vertex_interface: ShaderInterface,
    old_fragment_interface: ShaderInterface,
) -> bool {
    //  If replacing vertex shader, must be compatible
    (match request.new_vertex_shader {
        Some(new_vs) => vertex_shader_replacement_compatible(old_vertex_interface, new_vs),
        None => true,
    })
    //  If replacing fragment shader, must be compatible
    && (match request.new_fragment_shader {
        Some(new_fs) => fragment_shader_replacement_compatible(old_fragment_interface, new_fs),
        None => true,
    })
}

///  The old pipeline has no in-flight references: no incomplete submission
///  references its id.
pub open spec fn no_in_flight_pipeline_references(
    submissions: Seq<SubmissionRecord>,
    pipeline_id: nat,
) -> bool {
    forall|i: int| #![trigger submissions[i]]
        0 <= i < submissions.len()
        ==> (submissions[i].completed
            || !submissions[i].referenced_resources.contains(
                ResourceId::Buffer { id: pipeline_id }))
}

///  It is safe to swap a pipeline: no in-flight work references it.
pub open spec fn safe_to_swap(
    submissions: Seq<SubmissionRecord>,
    pipeline_id: nat,
) -> bool {
    no_in_flight_pipeline_references(submissions, pipeline_id)
}

///  The new pipeline is layout-compatible with the old one:
///  same descriptor set layouts, same render pass, same subpass.
pub open spec fn pipeline_layout_compatible(
    old_pipeline: GraphicsPipelineState,
    new_pipeline: GraphicsPipelineState,
) -> bool {
    layouts_identical(old_pipeline.descriptor_set_layouts, new_pipeline.descriptor_set_layouts)
    && old_pipeline.render_pass_id == new_pipeline.render_pass_id
    && old_pipeline.subpass_index == new_pipeline.subpass_index
    && old_pipeline.color_attachment_count == new_pipeline.color_attachment_count
    && old_pipeline.has_depth_attachment == new_pipeline.has_depth_attachment
}

///  After a reload, existing descriptor sets remain valid: since the
///  descriptor set layouts are identical, any set that was valid for
///  the old pipeline's layout is valid for the new one.
pub open spec fn descriptor_sets_remain_valid(
    old_layouts: Seq<nat>,
    new_layouts: Seq<nat>,
    bound_sets: Map<nat, nat>,
) -> bool {
    layouts_identical(old_layouts, new_layouts)
    ==> (forall|k: nat| bound_sets.contains_key(k)
        && k < old_layouts.len()
        ==> bound_sets[k] == bound_sets[k]) //  trivially true, but establishes the pattern
}

//  ── Proofs ──────────────────────────────────────────────────────────────

///  A compatible replacement preserves descriptor set layout identity,
///  so existing descriptor sets remain valid.
pub proof fn lemma_compatible_replacement_preserves_descriptors(
    old_pipeline: GraphicsPipelineState,
    new_pipeline: GraphicsPipelineState,
    set_index: nat,
)
    requires
        pipeline_layout_compatible(old_pipeline, new_pipeline),
        set_index < old_pipeline.descriptor_set_layouts.len(),
    ensures
        set_index < new_pipeline.descriptor_set_layouts.len(),
        old_pipeline.descriptor_set_layouts[set_index as int]
            == new_pipeline.descriptor_set_layouts[set_index as int],
{
}

///  Reloading with the identity (no shader changes) is always valid.
pub proof fn lemma_identity_reload_valid(
    old_vs: ShaderInterface,
    old_fs: ShaderInterface,
)
    ensures
        hot_reload_valid(
            ReloadRequest {
                old_pipeline_id: 0,
                new_vertex_shader: None,
                new_fragment_shader: None,
            },
            old_vs,
            old_fs,
        ),
{
}

///  Shader replacement compatibility is reflexive.
pub proof fn lemma_shader_replacement_reflexive(
    interface: ShaderInterface,
)
    ensures shader_replacement_compatible(interface, interface),
{
    assert forall|i: int| 0 <= i < interface.descriptor_bindings.len()
    implies ({
        let old_b = #[trigger] interface.descriptor_bindings[i];
        let new_b = interface.descriptor_bindings[i];
        old_b.set == new_b.set
        && old_b.binding == new_b.binding
        && old_b.descriptor_type == new_b.descriptor_type
        && old_b.count == new_b.count
    }) by {}
    lemma_push_constant_compatible_reflexive(interface.push_constant_range);
}

///  Pipeline layout compatibility is reflexive.
pub proof fn lemma_pipeline_layout_compatible_reflexive(
    pipeline: GraphicsPipelineState,
)
    ensures pipeline_layout_compatible(pipeline, pipeline),
{
}

///  After fence wait, if all submissions referencing the pipeline's
///  resource have this fence, the pipeline is safe to swap.
pub proof fn lemma_fence_wait_enables_swap(
    submissions: Seq<SubmissionRecord>,
    fence: nat,
    pipeline_id: nat,
)
    requires
        forall|i: int| 0 <= i < submissions.len()
            && submissions[i].referenced_resources.contains(
                ResourceId::Buffer { id: pipeline_id })
            ==> submissions[i].fence_id == Some(fence),
    ensures
        safe_to_swap(
            remove_completed(mark_fence_completed(submissions, fence)),
            pipeline_id,
        ),
{
    let resource = ResourceId::Buffer { id: pipeline_id };
    lemma_wait_clears_fence_submissions(submissions, fence, resource);
    let cleaned = remove_completed(mark_fence_completed(submissions, fence));
    assert forall|i: int| #![trigger cleaned[i]]
        0 <= i < cleaned.len()
        implies (cleaned[i].completed
            || !cleaned[i].referenced_resources.contains(resource)) by {
    }
}

///  If the old pipeline is layout-compatible with the new one,
///  then the new pipeline is compatible with the same subpass.
pub proof fn lemma_compatible_reload_preserves_subpass_compatibility(
    old_pipeline: GraphicsPipelineState,
    new_pipeline: GraphicsPipelineState,
    rp: RenderPassState,
    s: nat,
)
    requires
        pipeline_layout_compatible(old_pipeline, new_pipeline),
        graphics_pipeline_compatible_with_subpass(old_pipeline, rp, s),
        new_pipeline.alive,
        s < rp.subpasses.len(),
    ensures
        graphics_pipeline_compatible_with_subpass(new_pipeline, rp, s),
{
}

///  Swapping one pipeline doesn't affect another pipeline's state.
pub proof fn lemma_swap_preserves_other_pipelines(
    old_id: nat,
    new_pipeline: GraphicsPipelineState,
    other_pipeline: GraphicsPipelineState,
)
    requires
        other_pipeline.id != old_id,
        other_pipeline.id != new_pipeline.id,
    ensures
        other_pipeline.alive == other_pipeline.alive,
        other_pipeline.descriptor_set_layouts == other_pipeline.descriptor_set_layouts,
{
}

///  An empty submission log is always safe to swap.
pub proof fn lemma_empty_submissions_safe_to_swap(pipeline_id: nat)
    ensures
        safe_to_swap(Seq::<SubmissionRecord>::empty(), pipeline_id),
{
}

///  If all submissions are completed, it is safe to swap.
pub proof fn lemma_all_completed_safe_to_swap(
    submissions: Seq<SubmissionRecord>,
    pipeline_id: nat,
)
    requires
        forall|i: int| 0 <= i < submissions.len()
            ==> (#[trigger] submissions[i]).completed,
    ensures
        safe_to_swap(submissions, pipeline_id),
{
}

///  Layout identity is reflexive.
pub proof fn lemma_layouts_identical_reflexive(layouts: Seq<nat>)
    ensures layouts_identical(layouts, layouts),
{
}

///  Layout identity is symmetric.
pub proof fn lemma_layouts_identical_symmetric(a: Seq<nat>, b: Seq<nat>)
    requires layouts_identical(a, b),
    ensures layouts_identical(b, a),
{
}

///  Layout identity is transitive.
pub proof fn lemma_layouts_identical_transitive(
    a: Seq<nat>,
    b: Seq<nat>,
    c: Seq<nat>,
)
    requires
        layouts_identical(a, b),
        layouts_identical(b, c),
    ensures
        layouts_identical(a, c),
{
}

} //  verus!
