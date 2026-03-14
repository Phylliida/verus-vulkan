//! # Example: Ray Traced Sphere Scene
//!
//! Models a basic ray-traced scene with a single sphere:
//!   1. Create a BLAS with sphere geometry (AABB)
//!   2. Build the BLAS
//!   3. Create a TLAS referencing the BLAS instance
//!   4. Build the TLAS
//!   5. Create an RT pipeline with raygen + miss + closest-hit
//!   6. Validate a direct trace rays dispatch
//!   7. Validate an indirect trace rays dispatch (VK_KHR_ray_tracing_maintenance1)
//!
//! Proves that the full build→trace lifecycle is valid at each step.

use vstd::prelude::*;
use crate::acceleration_structure::*;
use crate::ray_tracing_pipeline::*;
use crate::ray_tracing_maintenance::*;

verus! {

// ── Scene Objects ───────────────────────────────────────────────────────

/// A BLAS containing a single AABB geometry (bounding the sphere).
pub open spec fn sphere_blas() -> AccelerationStructureState {
    AccelerationStructureState {
        id: 10,
        level: ASLevel::Bottom,
        geometries: seq![
            ASGeometryDesc {
                geometry_type: ASGeometryType::AABBs,
                primitive_count: 1,  // one sphere
                vertex_buffer: 200,
                index_buffer: None,
                transform_buffer: None,
            },
        ],
        instances: Seq::empty(),
        built: false,
        buffer_id: 201,
        scratch_buffer_id: 202,
        alive: true,
        generation: 0,
    }
}

/// A TLAS with a single instance referencing the sphere BLAS.
pub open spec fn scene_tlas() -> AccelerationStructureState {
    AccelerationStructureState {
        id: 20,
        level: ASLevel::Top,
        geometries: Seq::empty(),
        instances: seq![
            ASInstanceDesc {
                blas_id: 10,  // references sphere_blas
                transform: 0, // identity
                custom_index: 0,
                mask: 0xFF,
            },
        ],
        built: false,
        buffer_id: 301,
        scratch_buffer_id: 302,
        alive: true,
        generation: 0,
    }
}

/// An SBT with raygen (camera rays), miss (sky color), and closest-hit (sphere shading).
pub open spec fn sphere_sbt() -> ShaderBindingTable {
    ShaderBindingTable {
        ray_gen: seq![RayGenShader { id: 0 }],
        miss: seq![MissShader { id: 1 }],
        hit: seq![HitGroup {
            closest_hit: Some(2),
            any_hit: None,
            intersection: Some(3),  // custom sphere intersection
        }],
        callable: Seq::empty(),
        buffer_id: 400,
    }
}

/// An RT pipeline for the sphere scene.
pub open spec fn sphere_rt_pipeline() -> RayTracingPipelineState {
    RayTracingPipelineState {
        id: 50,
        max_recursion_depth: 1,  // no secondary rays
        shader_groups: seq![0, 1, 2],  // raygen, miss, hit
        sbt: sphere_sbt(),
        alive: true,
    }
}

// ── Step-by-step Proofs ─────────────────────────────────────────────────

/// Step 1: The sphere BLAS is well-formed (alive, bottom-level, has geometry).
pub proof fn step1_blas_well_formed()
    ensures
        blas_well_formed(sphere_blas()),
        !sphere_blas().built,
        all_geometries_non_empty(sphere_blas()),
{
}

/// Step 2: Build the BLAS. After building, it's still well-formed and now built.
pub proof fn step2_build_blas()
    ensures ({
        let built_blas = build_as_ghost(sphere_blas(), ASBuildMode::Build);
        blas_well_formed(built_blas)
        && built_blas.built
        && built_blas.generation == 1  // incremented from 0
        && built_blas.id == 10  // id preserved
    }),
{
    lemma_build_preserves_blas_well_formed(sphere_blas(), ASBuildMode::Build);
    lemma_build_makes_built(sphere_blas(), ASBuildMode::Build);
    lemma_build_increments_generation(sphere_blas(), ASBuildMode::Build);
    lemma_build_preserves_id(sphere_blas(), ASBuildMode::Build);
}

/// Step 3: The TLAS is well-formed.
pub proof fn step3_tlas_well_formed()
    ensures
        tlas_well_formed(scene_tlas()),
        !scene_tlas().built,
{
}

/// Step 4: After the BLAS is built, all BLAS references in the TLAS are valid.
/// Then build the TLAS itself.
pub proof fn step4_build_tlas()
    ensures ({
        let built_blas = build_as_ghost(sphere_blas(), ASBuildMode::Build);
        let blas_map = Map::empty().insert(10nat, built_blas);
        let built_tlas = build_as_ghost(scene_tlas(), ASBuildMode::Build);
        all_blas_references_valid(scene_tlas(), blas_map)
        && tlas_well_formed(built_tlas)
        && built_tlas.built
    }),
{
    let built_blas = build_as_ghost(sphere_blas(), ASBuildMode::Build);
    let blas_map = Map::<nat, AccelerationStructureState>::empty().insert(10nat, built_blas);

    // Prove BLAS references valid: instance 0 references blas_id=10, which is in the map and built
    assert forall|i: nat|
        i < scene_tlas().instances.len()
    implies
        blas_map.contains_key(#[trigger] scene_tlas().instances[i as int].blas_id)
        && blas_map[scene_tlas().instances[i as int].blas_id].built
        && blas_map[scene_tlas().instances[i as int].blas_id].alive
    by {
        assert(i == 0);
        lemma_build_makes_built(sphere_blas(), ASBuildMode::Build);
        lemma_build_preserves_alive(sphere_blas(), ASBuildMode::Build);
    }

    lemma_build_preserves_tlas_well_formed(scene_tlas(), ASBuildMode::Build);
    lemma_build_makes_built(scene_tlas(), ASBuildMode::Build);
}

/// Step 5: The RT pipeline is well-formed (alive, has groups, SBT well-formed).
pub proof fn step5_pipeline_well_formed()
    ensures
        rt_pipeline_well_formed(sphere_rt_pipeline()),
        sbt_well_formed(sphere_sbt()),
        sbt_covers_pipeline(sphere_sbt(), sphere_rt_pipeline()),
{
}

/// Step 6: Direct trace rays is valid.
/// Pipeline alive + TLAS built + positive dispatch dims + SBT covers pipeline.
pub proof fn step6_trace_rays_valid()
    ensures ({
        let built_tlas = build_as_ghost(scene_tlas(), ASBuildMode::Build);
        let params = TraceRaysParams { width: 1920, height: 1080, depth: 1 };
        trace_rays_valid(sphere_rt_pipeline(), built_tlas, params)
    }),
{
    let built_tlas = build_as_ghost(scene_tlas(), ASBuildMode::Build);
    let params = TraceRaysParams { width: 1920, height: 1080, depth: 1 };
    lemma_build_preserves_tlas_well_formed(scene_tlas(), ASBuildMode::Build);
    lemma_build_makes_built(scene_tlas(), ASBuildMode::Build);
}

/// Step 7: Indirect trace rays (VK_KHR_ray_tracing_maintenance1).
/// Same scene but dispatched indirectly from a GPU buffer.
pub proof fn step7_indirect_trace_rays()
    ensures ({
        let built_tlas = build_as_ghost(scene_tlas(), ASBuildMode::Build);
        let params = IndirectTraceRaysParams {
            indirect_buffer_id: 500,
            indirect_offset: 0,  // 4-byte aligned, offset + 16 <= buffer_size
        };
        indirect_trace_rays_valid(sphere_rt_pipeline(), built_tlas, 256, params)
    }),
{
    lemma_build_preserves_tlas_well_formed(scene_tlas(), ASBuildMode::Build);
    lemma_build_makes_built(scene_tlas(), ASBuildMode::Build);
}

/// Bonus: Validate SBT regions for vkCmdTraceRaysKHR2 (maintenance1 path).
pub proof fn step8_trace_rays_with_regions()
    ensures ({
        let built_tlas = build_as_ghost(scene_tlas(), ASBuildMode::Build);
        let raygen = StridedDeviceAddressRegion { device_address: 4096, stride: 32, size: 32 };
        let miss   = StridedDeviceAddressRegion { device_address: 8192, stride: 32, size: 32 };
        let hit    = StridedDeviceAddressRegion { device_address: 12288, stride: 32, size: 32 };
        let callable = StridedDeviceAddressRegion { device_address: 16384, stride: 32, size: 32 };
        let params = TraceRaysParams { width: 1920, height: 1080, depth: 1 };
        // raygen.stride == raygen.size (single entry)
        raygen.stride == raygen.size
        && trace_rays_with_regions_valid(
            sphere_rt_pipeline(), built_tlas, raygen, miss, hit, callable, params,
        )
    }),
{
    lemma_build_preserves_tlas_well_formed(scene_tlas(), ASBuildMode::Build);
    lemma_build_makes_built(scene_tlas(), ASBuildMode::Build);
}

/// Bonus: The maintenance1 state ties to our pipeline.
pub proof fn step9_maintenance1_state()
    ensures ({
        let m1 = create_maintenance1_state(50, false, 32);
        maintenance1_well_formed(m1, sphere_rt_pipeline())
        && !inline_ray_tracing_enabled(m1)
        && maintenance1_ray_hit_attribute_valid(m1, 16)
    }),
{
}

} // verus!
