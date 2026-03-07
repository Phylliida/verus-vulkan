use vstd::prelude::*;
use crate::descriptor::*;
use crate::image_layout::*;
use crate::pipeline::*;
use crate::recording::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// A single vertex shader input attribute.
///
/// In Vulkan, each vertex shader input has a location and a format.
/// The pipeline's vertex input state must provide a matching attribute
/// at each location, or the shader reads garbage.
pub struct ShaderInputAttribute {
    /// The location index in the shader (layout(location = N)).
    pub location: nat,
    /// Format identifier (numeric, matching VkFormat).
    pub format: nat,
}

/// A single descriptor binding expected by a shader.
///
/// The shader declares `layout(set = S, binding = B)` for each resource.
/// The pipeline layout's descriptor set layouts must contain matching
/// bindings, or descriptor writes go to the wrong slot.
pub struct ShaderDescriptorBinding {
    /// Descriptor set index.
    pub set: nat,
    /// Binding number within that set.
    pub binding: nat,
    /// Expected descriptor type.
    pub descriptor_type: DescriptorType,
    /// Number of descriptors (array size; 1 for non-arrays).
    pub count: nat,
}

/// A push constant range used by a shader stage.
pub struct PushConstantRange {
    /// Offset in bytes from the start of push constant memory.
    pub offset: nat,
    /// Size in bytes.
    pub size: nat,
}

/// The interface of a compiled shader module, extracted from SPIR-V reflection.
///
/// This is established at create_shader_module time and is immutable.
/// Pipeline creation verifies that the pipeline state matches this interface.
pub struct ShaderInterface {
    /// Vertex inputs (only meaningful for vertex shaders).
    pub inputs: Seq<ShaderInputAttribute>,
    /// Fragment outputs count (only meaningful for fragment shaders).
    pub output_count: nat,
    /// Descriptor bindings used by this shader.
    pub descriptor_bindings: Seq<ShaderDescriptorBinding>,
    /// Push constant range, if any.
    pub push_constant_range: Option<PushConstantRange>,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// Two formats are compatible (same numeric format ID).
/// In practice this would check component count, bit width, and signedness.
pub open spec fn format_compatible(shader_format: nat, pipeline_format: nat) -> bool {
    shader_format == pipeline_format
}

/// Every vertex shader input has a matching vertex attribute with
/// the same location and compatible format.
pub open spec fn vertex_inputs_match(
    shader: ShaderInterface,
    vertex_attributes: Seq<ShaderInputAttribute>,
) -> bool {
    forall|i: int| 0 <= i < shader.inputs.len() ==> {
        let input = #[trigger] shader.inputs[i];
        exists|j: int| 0 <= j < vertex_attributes.len()
            && vertex_attributes[j].location == input.location
            && format_compatible(vertex_attributes[j].format, input.format)
    }
}

/// Every descriptor binding declared by the shader is present in
/// the corresponding descriptor set layout with matching type and count.
pub open spec fn descriptor_bindings_match_layouts(
    shader_bindings: Seq<ShaderDescriptorBinding>,
    set_layouts: Seq<DescriptorSetLayoutState>,
) -> bool {
    forall|i: int| 0 <= i < shader_bindings.len() ==> {
        let b = #[trigger] shader_bindings[i];
        b.set < set_layouts.len()
        && layout_has_binding(set_layouts[b.set as int], b.binding, b.descriptor_type, b.count)
    }
}

/// A push constant range is covered: the shader's range fits within
/// a pipeline push constant range.
pub open spec fn push_constants_covered(
    shader_range: Option<PushConstantRange>,
    pipeline_ranges: Seq<PushConstantRange>,
) -> bool {
    match shader_range {
        None => true,
        Some(sr) => exists|j: int| 0 <= j < pipeline_ranges.len()
            && pipeline_ranges[j].offset <= sr.offset
            && sr.offset + sr.size <= pipeline_ranges[j].offset + pipeline_ranges[j].size,
    }
}

/// Fragment output count matches the color attachment count.
pub open spec fn output_count_matches(
    shader: ShaderInterface,
    color_attachment_count: nat,
) -> bool {
    shader.output_count == color_attachment_count
}

/// Full shader-pipeline compatibility:
/// - Vertex inputs match pipeline vertex attributes
/// - Descriptor bindings match pipeline descriptor set layouts
/// - Push constants are covered
pub open spec fn shader_pipeline_compatible(
    vertex_shader: ShaderInterface,
    fragment_shader: ShaderInterface,
    vertex_attributes: Seq<ShaderInputAttribute>,
    set_layouts: Seq<DescriptorSetLayoutState>,
    push_ranges: Seq<PushConstantRange>,
    color_attachment_count: nat,
) -> bool {
    // Vertex inputs
    vertex_inputs_match(vertex_shader, vertex_attributes)
    // Vertex shader descriptor bindings
    && descriptor_bindings_match_layouts(vertex_shader.descriptor_bindings, set_layouts)
    // Fragment shader descriptor bindings
    && descriptor_bindings_match_layouts(fragment_shader.descriptor_bindings, set_layouts)
    // Push constants for both shaders
    && push_constants_covered(vertex_shader.push_constant_range, push_ranges)
    && push_constants_covered(fragment_shader.push_constant_range, push_ranges)
    // Fragment output count
    && output_count_matches(fragment_shader, color_attachment_count)
}

/// All descriptor bindings from both shaders combined.
pub open spec fn all_shader_bindings(
    vertex_shader: ShaderInterface,
    fragment_shader: ShaderInterface,
) -> Seq<ShaderDescriptorBinding> {
    vertex_shader.descriptor_bindings + fragment_shader.descriptor_bindings
}

/// A bound descriptor set satisfies a shader binding:
/// the set has a binding with matching type and count.
pub open spec fn descriptor_set_satisfies_binding(
    dset: DescriptorSetState,
    layout: DescriptorSetLayoutState,
    binding: ShaderDescriptorBinding,
) -> bool {
    layout_has_binding(layout, binding.binding, binding.descriptor_type, binding.count)
    && dset.bindings.contains_key(binding.binding)
    && !(dset.bindings[binding.binding] === DescriptorBinding::Empty)
}

/// All shader bindings are satisfied by the currently bound descriptor sets.
pub open spec fn all_bindings_satisfied(
    shader_bindings: Seq<ShaderDescriptorBinding>,
    bound_sets: Map<nat, DescriptorSetState>,
    set_layouts: Seq<DescriptorSetLayoutState>,
) -> bool {
    forall|i: int| 0 <= i < shader_bindings.len() ==> {
        let b = #[trigger] shader_bindings[i];
        b.set < set_layouts.len()
        && bound_sets.contains_key(b.set)
        && descriptor_set_satisfies_binding(bound_sets[b.set], set_layouts[b.set as int], b)
    }
}

/// Two push constant ranges are compatible: the new range covers
/// at least as much as the old range.
pub open spec fn push_constant_range_compatible(
    old_range: Option<PushConstantRange>,
    new_range: Option<PushConstantRange>,
) -> bool {
    match (old_range, new_range) {
        (None, _) => true,
        (Some(_), None) => false,
        (Some(old), Some(new)) =>
            new.offset <= old.offset
            && old.offset + old.size <= new.offset + new.size,
    }
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// Format compatibility is reflexive.
pub proof fn lemma_format_compatible_reflexive(f: nat)
    ensures format_compatible(f, f),
{
}

/// Format compatibility is symmetric.
pub proof fn lemma_format_compatible_symmetric(a: nat, b: nat)
    requires format_compatible(a, b),
    ensures format_compatible(b, a),
{
}

/// Full shader-pipeline compatibility implies vertex inputs match.
pub proof fn lemma_compatible_implies_vertex_match(
    vs: ShaderInterface,
    fs: ShaderInterface,
    attrs: Seq<ShaderInputAttribute>,
    layouts: Seq<DescriptorSetLayoutState>,
    push_ranges: Seq<PushConstantRange>,
    color_count: nat,
)
    requires shader_pipeline_compatible(vs, fs, attrs, layouts, push_ranges, color_count),
    ensures vertex_inputs_match(vs, attrs),
{
}

/// Full shader-pipeline compatibility implies descriptor bindings match
/// for both vertex and fragment shaders.
pub proof fn lemma_compatible_implies_descriptor_match(
    vs: ShaderInterface,
    fs: ShaderInterface,
    attrs: Seq<ShaderInputAttribute>,
    layouts: Seq<DescriptorSetLayoutState>,
    push_ranges: Seq<PushConstantRange>,
    color_count: nat,
)
    requires shader_pipeline_compatible(vs, fs, attrs, layouts, push_ranges, color_count),
    ensures
        descriptor_bindings_match_layouts(vs.descriptor_bindings, layouts),
        descriptor_bindings_match_layouts(fs.descriptor_bindings, layouts),
{
}

/// Full compatibility implies output count matches.
pub proof fn lemma_compatible_implies_output_match(
    vs: ShaderInterface,
    fs: ShaderInterface,
    attrs: Seq<ShaderInputAttribute>,
    layouts: Seq<DescriptorSetLayoutState>,
    push_ranges: Seq<PushConstantRange>,
    color_count: nat,
)
    requires shader_pipeline_compatible(vs, fs, attrs, layouts, push_ranges, color_count),
    ensures output_count_matches(fs, color_count),
{
}

/// If a descriptor set is fully bound and the layout matches a shader binding,
/// then that binding is satisfied.
pub proof fn lemma_fully_bound_satisfies_binding(
    dset: DescriptorSetState,
    layout: DescriptorSetLayoutState,
    binding: ShaderDescriptorBinding,
)
    requires
        descriptor_set_fully_bound(dset, layout),
        layout_has_binding(layout, binding.binding, binding.descriptor_type, binding.count),
    ensures
        descriptor_set_satisfies_binding(dset, layout, binding),
{
    // layout_has_binding gives us exists|i| layout.bindings[i].binding == binding.binding
    let witness = choose|i: int| 0 <= i < layout.bindings.len()
        && layout.bindings[i].binding == binding.binding
        && layout.bindings[i].descriptor_type == binding.descriptor_type
        && layout.bindings[i].descriptor_count == binding.count;
    // descriptor_set_fully_bound says for all layout bindings, dset has non-Empty entry
    assert(layout.bindings[witness].binding == binding.binding);
    assert(dset.bindings.contains_key(binding.binding));
    assert(!(dset.bindings[binding.binding] === DescriptorBinding::Empty));
}

/// An empty shader (no inputs) matches any attribute set.
pub proof fn lemma_empty_shader_matches_any(
    attrs: Seq<ShaderInputAttribute>,
)
    ensures
        vertex_inputs_match(
            ShaderInterface {
                inputs: Seq::empty(),
                output_count: 0,
                descriptor_bindings: Seq::empty(),
                push_constant_range: None,
            },
            attrs,
        ),
{
}

/// If the vertex attributes contain a matching entry for a single-input
/// shader, then vertex_inputs_match holds.
pub proof fn lemma_single_input_match(
    input: ShaderInputAttribute,
    attrs: Seq<ShaderInputAttribute>,
    witness_idx: int,
)
    requires
        0 <= witness_idx < attrs.len(),
        attrs[witness_idx].location == input.location,
        format_compatible(attrs[witness_idx].format, input.format),
    ensures
        vertex_inputs_match(
            ShaderInterface {
                inputs: seq![input],
                output_count: 0,
                descriptor_bindings: Seq::empty(),
                push_constant_range: None,
            },
            attrs,
        ),
{
}

/// Push constant range compatibility is reflexive.
pub proof fn lemma_push_constant_compatible_reflexive(r: Option<PushConstantRange>)
    ensures push_constant_range_compatible(r, r),
{
}

/// If no shader uses push constants, any pipeline ranges are fine.
pub proof fn lemma_no_push_constants_always_covered(
    pipeline_ranges: Seq<PushConstantRange>,
)
    ensures push_constants_covered(None, pipeline_ranges),
{
}

/// All bindings satisfied implies each individual binding is satisfied.
pub proof fn lemma_all_bindings_satisfied_individual(
    shader_bindings: Seq<ShaderDescriptorBinding>,
    bound_sets: Map<nat, DescriptorSetState>,
    set_layouts: Seq<DescriptorSetLayoutState>,
    k: int,
)
    requires
        all_bindings_satisfied(shader_bindings, bound_sets, set_layouts),
        0 <= k < shader_bindings.len(),
    ensures ({
        let b = shader_bindings[k];
        b.set < set_layouts.len()
        && bound_sets.contains_key(b.set)
        && descriptor_set_satisfies_binding(bound_sets[b.set], set_layouts[b.set as int], b)
    }),
{
}

} // verus!
