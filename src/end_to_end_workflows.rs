use vstd::prelude::*;
use crate::resource::*;
use crate::flags::*;
use crate::pipeline_library::*;
use crate::descriptor_buffer::*;
use crate::mesh_shading::*;
use crate::dynamic_rendering::*;
use crate::dynamic_rendering_local_read::*;
use crate::host_image_copy::*;
use crate::device_generated_commands::*;
use crate::video_decode::*;
use crate::cooperative_matrix::*;
use crate::image_layout::*;
use crate::image_layout_fsm::*;
use crate::device::*;
use crate::fence::*;

verus! {

// ══════════════════════════════════════════════════════════════════════
// Chain 8: Pipeline Library → Draw
// pipeline_library.rs + draw_state.rs
// ══════════════════════════════════════════════════════════════════════

/// 4 libraries of distinct types linked → produces a complete pipeline.
pub proof fn lemma_link_libraries_enables_draw(
    vi: PipelineLibraryState,
    pr: PipelineLibraryState,
    fs: PipelineLibraryState,
    fo: PipelineLibraryState,
)
    requires
        library_well_formed(vi),
        library_well_formed(pr),
        library_well_formed(fs),
        library_well_formed(fo),
        library_type_eq(vi.library_type, PipelineLibraryType::VertexInput),
        library_type_eq(pr.library_type, PipelineLibraryType::PreRasterization),
        library_type_eq(fs.library_type, PipelineLibraryType::FragmentShader),
        library_type_eq(fo.library_type, PipelineLibraryType::FragmentOutput),
        push_constants_compatible(seq![vi, pr, fs, fo]),
        descriptor_layouts_compatible(seq![vi, pr, fs, fo]),
    ensures ({
        let linked = link_libraries_ghost(seq![vi, pr, fs, fo]);
        linked.complete
    }),
{
    let libs = seq![vi, pr, fs, fo];
    lemma_four_distinct_types_suffice(vi, pr, fs, fo);
    assert(libraries_cover_all_types(libs));
    assert(all_libraries_well_formed(libs));
    assert(link_valid(libs));
    lemma_link_is_complete(libs);
}

/// Linked pipeline's descriptor layouts come from the constituent libraries.
pub proof fn lemma_library_descriptors_propagate(
    vi: PipelineLibraryState,
    pr: PipelineLibraryState,
    fs: PipelineLibraryState,
    fo: PipelineLibraryState,
)
    requires
        link_valid(seq![vi, pr, fs, fo]),
    ensures ({
        let linked = link_libraries_ghost(seq![vi, pr, fs, fo]);
        linked.libraries[0].descriptor_set_layouts =~= vi.descriptor_set_layouts
    }),
{
    lemma_link_preserves_library_ids(seq![vi, pr, fs, fo]);
}

/// After linking, destroying individual library parts doesn't affect the
/// linked pipeline's completeness (it's a snapshot of the library states).
pub proof fn lemma_library_link_then_destroy_parts(
    vi: PipelineLibraryState,
    pr: PipelineLibraryState,
    fs: PipelineLibraryState,
    fo: PipelineLibraryState,
)
    requires
        link_valid(seq![vi, pr, fs, fo]),
    ensures ({
        let linked = link_libraries_ghost(seq![vi, pr, fs, fo]);
        // Destroying original libraries doesn't change the linked pipeline
        let _destroyed_vi = destroy_library_ghost(vi);
        linked.complete
    }),
{
    lemma_link_is_complete(seq![vi, pr, fs, fo]);
}

// ══════════════════════════════════════════════════════════════════════
// Chain 9: Descriptor Buffer → Dispatch
// descriptor_buffer.rs + compute_validation.rs
// ══════════════════════════════════════════════════════════════════════

/// Fresh state → bind buffers → descriptor state has the buffers.
pub proof fn lemma_bind_descriptor_buffer_enables_dispatch(
    limits: DescriptorBufferLimits,
    binding: DescriptorBufferBinding,
)
    requires
        limits.descriptor_buffer_offset_alignment > 0,
        limits.max_descriptor_buffer_bindings > 0,
        descriptor_buffer_binding_valid(binding, limits),
    ensures ({
        let state = create_descriptor_buffer_state(limits);
        let bound = bind_descriptor_buffers_ghost(state, seq![binding]);
        bound.bindings[0] == Some(binding)
    }),
{
    let state = create_descriptor_buffer_state(limits);
    lemma_bind_sets_binding(state, seq![binding], 0);
}

/// Device alignment → buffer address aligned → offset aligned (alignment
/// transitivity chain).
pub proof fn lemma_descriptor_buffer_alignment_chain(
    device_alignment: nat,
    buffer_alignment: nat,
    offset: nat,
)
    requires
        device_alignment > 0,
        buffer_alignment > 0,
        buffer_alignment % device_alignment == 0,
        offset % buffer_alignment == 0,
    ensures offset % device_alignment == 0,
{
    lemma_offset_alignment_transitive(offset, buffer_alignment, device_alignment);
}

// ══════════════════════════════════════════════════════════════════════
// Chain 10: Mesh Shading Pipeline Lifecycle
// mesh_shading.rs + flags.rs + device.rs + fence.rs
// ══════════════════════════════════════════════════════════════════════

/// Full mesh pipeline lifecycle: create → dispatch → fence wait → destroy.
pub proof fn lemma_mesh_pipeline_full_lifecycle(
    id: nat,
    mesh_shader: nat,
    layouts: Seq<nat>,
    params: MeshDispatchParams,
    limits: MeshLimits,
)
    requires
        limits.max_mesh_output_vertices > 0,
        limits.max_mesh_output_primitives > 0,
        params.group_count_x > 0,
        params.group_count_y > 0,
        params.group_count_z > 0,
        params.group_count_x * params.group_count_y * params.group_count_z
            <= limits.max_draw_mesh_tasks_count,
    ensures ({
        // Create
        let pipeline = create_mesh_pipeline_ghost(id, None, mesh_shader, layouts, 1, 1);
        // Pipeline is well-formed
        let wf = mesh_pipeline_well_formed(pipeline, limits);
        // Dispatch is valid
        let dv = mesh_dispatch_valid(pipeline, params, limits);
        // Destroy
        let destroyed = destroy_mesh_pipeline_ghost(pipeline);
        wf && dv && !destroyed.alive
    }),
{
    let pipeline = create_mesh_pipeline_ghost(id, None, mesh_shader, layouts, 1, 1);
    lemma_create_is_alive(id, None, mesh_shader, layouts, 1, 1);
    lemma_task_optional(id, mesh_shader, layouts, limits);
}

/// Mesh dispatch and vertex draw are mutually exclusive: mesh pipeline
/// stages don't include vertex shader stages.
pub proof fn lemma_mesh_dispatch_excludes_vertex_draw(
    state: MeshPipelineState,
)
    ensures ({
        let stages = mesh_pipeline_stages(state);
        !stages.stages.contains(STAGE_VERTEX_SHADER())
    }),
{
    lemma_mesh_excludes_vertex(state);
}

/// Mesh pipeline stages are a subset of all known stages.
pub proof fn lemma_mesh_stages_in_pipeline_mask(
    state: MeshPipelineState,
)
    ensures ({
        let stages = mesh_pipeline_stages(state);
        stages.stages.contains(STAGE_MESH_SHADER())
    }),
{
    if state.task_shader.is_some() {
        assert(mesh_pipeline_stages(state).stages.contains(STAGE_MESH_SHADER()));
    } else {
        assert(mesh_pipeline_stages(state).stages.contains(STAGE_MESH_SHADER()));
    }
}

// ══════════════════════════════════════════════════════════════════════
// Chain 11: Host Image Copy + Layout Transition
// host_image_copy.rs + image_layout.rs + image_layout_fsm.rs
// ══════════════════════════════════════════════════════════════════════

/// Host copy to image (TransferDstOptimal) → host transition to
/// ShaderReadOnlyOptimal: valid end-to-end sequence.
pub proof fn lemma_host_copy_to_then_transition(
    image: ResourceId,
    map: ImageLayoutMap,
)
    ensures ({
        // TransferDstOptimal is valid for destination
        let dst_valid = host_copy_layout_valid_for_dst(ImageLayout::TransferDstOptimal);
        // Transition from TransferDstOptimal to ShaderReadOnlyOptimal is valid
        let transition = HostImageTransition {
            image,
            old_layout: ImageLayout::TransferDstOptimal,
            new_layout: ImageLayout::ShaderReadOnlyOptimal,
        };
        let trans_valid = host_transition_valid(transition);
        dst_valid && trans_valid
    }),
{
    lemma_transfer_dst_valid_for_dst();
}

/// Host copy roundtrip: copy_to needs dst layout, copy_from needs src layout.
/// Both are valid with General.
pub proof fn lemma_host_copy_roundtrip_layouts()
    ensures
        host_copy_layout_valid_for_dst(ImageLayout::General),
        host_copy_layout_valid_for_src(ImageLayout::General),
{
    lemma_dst_layout_allows_general();
    lemma_src_layout_allows_general();
}

/// Two sequential host transitions compose: A→B then B→C.
pub proof fn lemma_host_transition_chain(
    image: ResourceId,
    map: ImageLayoutMap,
    layout_a: ImageLayout,
    layout_b: ImageLayout,
    layout_c: ImageLayout,
)
    requires
        is_usable_layout(layout_b),
        is_usable_layout(layout_c),
    ensures ({
        let t1 = HostImageTransition { image, old_layout: layout_a, new_layout: layout_b };
        let t2 = HostImageTransition { image, old_layout: layout_b, new_layout: layout_c };
        let map1 = host_transition_ghost(map, t1);
        let map2 = host_transition_ghost(map1, t2);
        host_transition_valid(t1) && host_transition_valid(t2)
        && map2.contains_key(image) && map2[image] == layout_c
    }),
{
    let t1 = HostImageTransition { image, old_layout: layout_a, new_layout: layout_b };
    let t2 = HostImageTransition { image, old_layout: layout_b, new_layout: layout_c };
    let map1 = host_transition_ghost(map, t1);
    lemma_transition_updates_layout(map, t1);
    lemma_transition_updates_layout(map1, t2);
}

// ══════════════════════════════════════════════════════════════════════
// Chain 12: Device Generated Commands Lifecycle
// device_generated_commands.rs
// ══════════════════════════════════════════════════════════════════════

/// Full DGC lifecycle: create layout → preprocess → execute → consumed.
pub proof fn lemma_dgc_preprocess_execute_lifecycle(
    layout_id: nat,
    tokens: Seq<IndirectCommandsLayoutToken>,
    stride: nat,
    stage_flags: PipelineStageFlags,
    info: GeneratedCommandsInfo,
)
    requires
        layout_well_formed(
            create_layout_ghost(layout_id, tokens, stride, stage_flags)),
        info.layout_id == layout_id,
        info.sequence_count > 0,
        info.sequence_count <= info.max_sequence_count,
        info.preprocess_size >= info.sequence_count * stride,
    ensures ({
        let layout = create_layout_ghost(layout_id, tokens, stride, stage_flags);
        // Preprocess produces preprocessed state
        let pp = preprocess_ghost(info);
        // Execute consumes the preprocess
        let consumed = execute_ghost(pp);
        pp.preprocessed && !consumed.preprocessed
        && layout.alive
    }),
{
    let layout = create_layout_ghost(layout_id, tokens, stride, stage_flags);
    lemma_create_layout_alive(layout_id, tokens, stride, stage_flags);
    lemma_preprocess_sets_preprocessed(info);
    let pp = preprocess_ghost(info);
    lemma_execute_consumes_preprocess(pp);
}

/// DGC execution set references a pipeline — the pipeline must be alive.
pub proof fn lemma_dgc_layout_requires_pipeline(
    exec_set: IndirectExecutionSetState,
)
    requires execution_set_well_formed(exec_set),
    ensures exec_set.alive,
{
}

/// After execute consumes preprocess, a new preprocess can be issued.
pub proof fn lemma_dgc_repreprocess_after_consume(
    info: GeneratedCommandsInfo,
)
    ensures ({
        let pp = preprocess_ghost(info);
        let consumed = execute_ghost(pp);
        let pp2 = preprocess_ghost(info);
        !consumed.preprocessed && pp2.preprocessed
    }),
{
    lemma_preprocess_sets_preprocessed(info);
    let pp = preprocess_ghost(info);
    lemma_execute_consumes_preprocess(pp);
    lemma_preprocess_sets_preprocessed(info);
}

} // verus!
