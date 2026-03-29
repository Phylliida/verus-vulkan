use vstd::prelude::*;

verus! {

//  ── Types ──────────────────────────────────────────────────────────────

///  Geometry type in a bottom-level acceleration structure.
pub enum ASGeometryType {
    Triangles,
    AABBs,
}

///  Description of a single geometry in a BLAS.
pub struct ASGeometryDesc {
    ///  Type of geometry (triangles or AABBs).
    pub geometry_type: ASGeometryType,
    ///  Number of primitives.
    pub primitive_count: nat,
    ///  Buffer holding vertex data.
    pub vertex_buffer: nat,
    ///  Optional index buffer.
    pub index_buffer: Option<nat>,
    ///  Optional transform buffer.
    pub transform_buffer: Option<nat>,
}

///  Acceleration structure level.
pub enum ASLevel {
    Bottom,
    Top,
}

///  Build mode for an acceleration structure.
pub enum ASBuildMode {
    ///  Full build from scratch.
    Build,
    ///  In-place update (same geometry count, may change positions).
    Update,
}

///  An instance in a top-level acceleration structure referencing a BLAS.
pub struct ASInstanceDesc {
    ///  ID of the BLAS this instance references.
    pub blas_id: nat,
    ///  Transform identifier.
    pub transform: nat,
    ///  Custom index for shader access.
    pub custom_index: nat,
    ///  Visibility mask.
    pub mask: nat,
}

///  Ghost state for a VkAccelerationStructureKHR.
pub struct AccelerationStructureState {
    ///  Unique identifier.
    pub id: nat,
    ///  Whether this is a BLAS or TLAS.
    pub level: ASLevel,
    ///  Geometries (only for BLAS).
    pub geometries: Seq<ASGeometryDesc>,
    ///  Instances (only for TLAS).
    pub instances: Seq<ASInstanceDesc>,
    ///  Whether the AS has been built at least once.
    pub built: bool,
    ///  Buffer holding the AS data.
    pub buffer_id: nat,
    ///  Scratch buffer used during build.
    pub scratch_buffer_id: nat,
    ///  False after destruction.
    pub alive: bool,
    ///  Build generation counter.
    pub generation: nat,
}

//  ── Spec Functions ──────────────────────────────────────────────────

///  A bottom-level AS is well-formed: alive, correct level, has geometries.
pub open spec fn blas_well_formed(as_state: AccelerationStructureState) -> bool {
    as_state.alive
    && matches!(as_state.level, ASLevel::Bottom)
    && as_state.geometries.len() > 0
    && as_state.instances.len() == 0
}

///  A top-level AS is well-formed: alive, correct level, has instances.
pub open spec fn tlas_well_formed(as_state: AccelerationStructureState) -> bool {
    as_state.alive
    && matches!(as_state.level, ASLevel::Top)
    && as_state.instances.len() > 0
    && as_state.geometries.len() == 0
}

///  An AS is well-formed (BLAS or TLAS).
pub open spec fn as_well_formed(as_state: AccelerationStructureState) -> bool {
    as_state.alive
    && (blas_well_formed(as_state) || tlas_well_formed(as_state))
}

///  All BLAS references in a TLAS are valid (exist in map and are built).
pub open spec fn all_blas_references_valid(
    tlas: AccelerationStructureState,
    blas_map: Map<nat, AccelerationStructureState>,
) -> bool {
    forall|i: nat|
        #![trigger tlas.instances[i as int]]
        i < tlas.instances.len()
        ==> (
            blas_map.contains_key(tlas.instances[i as int].blas_id)
            && blas_map[tlas.instances[i as int].blas_id].built
            && blas_map[tlas.instances[i as int].blas_id].alive
        )
}

///  Ghost update: build an acceleration structure.
pub open spec fn build_as_ghost(
    as_state: AccelerationStructureState,
    mode: ASBuildMode,
) -> AccelerationStructureState
    recommends as_state.alive,
{
    AccelerationStructureState {
        built: true,
        generation: as_state.generation + 1,
        ..as_state
    }
}

///  Ghost update: destroy an acceleration structure.
pub open spec fn destroy_as_ghost(
    as_state: AccelerationStructureState,
) -> AccelerationStructureState
    recommends as_state.alive,
{
    AccelerationStructureState {
        alive: false,
        ..as_state
    }
}

///  The AS's storage buffer and scratch buffer must be alive.
pub open spec fn as_buffers_valid(
    as_state: AccelerationStructureState,
    live_buffers: Set<nat>,
) -> bool {
    live_buffers.contains(as_state.buffer_id)
    && live_buffers.contains(as_state.scratch_buffer_id)
}

///  Collect all buffer IDs referenced by geometry descriptions.
pub open spec fn as_geometry_buffer_refs(
    as_state: AccelerationStructureState,
) -> Set<nat> {
    Set::new(|buf_id: nat|
        exists|i: nat|
            #![trigger as_state.geometries[i as int]]
            i < as_state.geometries.len()
            && (as_state.geometries[i as int].vertex_buffer == buf_id
                || as_state.geometries[i as int].index_buffer == Some(buf_id)
                || as_state.geometries[i as int].transform_buffer == Some(buf_id))
    )
}

///  All geometry primitives have non-zero count.
pub open spec fn all_geometries_non_empty(
    as_state: AccelerationStructureState,
) -> bool {
    forall|i: nat|
        #![trigger as_state.geometries[i as int]]
        i < as_state.geometries.len()
        ==> as_state.geometries[i as int].primitive_count > 0
}

///  Update mode preserves geometry count.
pub open spec fn update_preserves_structure(
    old: AccelerationStructureState,
    new: AccelerationStructureState,
) -> bool {
    old.geometries.len() == new.geometries.len()
    && old.instances.len() == new.instances.len()
    && old.level == new.level
}

///  All BLAS IDs referenced by instances are distinct from the TLAS ID.
pub open spec fn tlas_blas_ids_distinct(
    tlas: AccelerationStructureState,
) -> bool {
    forall|i: nat|
        #![trigger tlas.instances[i as int]]
        i < tlas.instances.len()
        ==> tlas.instances[i as int].blas_id != tlas.id
}

//  ── Proofs ──────────────────────────────────────────────────────────

///  Building an AS sets the built flag to true.
pub proof fn lemma_build_makes_built(
    as_state: AccelerationStructureState,
    mode: ASBuildMode,
)
    ensures build_as_ghost(as_state, mode).built,
{
}

///  Destroying an AS sets alive to false.
///  Caller must prove the AS is alive before destroying.
pub proof fn lemma_destroy_invalidates(
    as_state: AccelerationStructureState,
)
    requires as_state.alive,
    ensures !destroy_as_ghost(as_state).alive,
{
}

///  An AS cannot be both BLAS and TLAS.
pub proof fn lemma_blas_tlas_exclusive(as_state: AccelerationStructureState)
    requires as_well_formed(as_state),
    ensures
        !(blas_well_formed(as_state) && tlas_well_formed(as_state)),
{
    if blas_well_formed(as_state) && tlas_well_formed(as_state) {
        //  BLAS requires instances.len() == 0, TLAS requires instances.len() > 0
        assert(as_state.instances.len() == 0);
        assert(as_state.instances.len() > 0);
    }
}

///  If a TLAS is well-formed with valid BLAS refs, all referenced BLASes are built.
pub proof fn lemma_tlas_requires_built_blas(
    tlas: AccelerationStructureState,
    blas_map: Map<nat, AccelerationStructureState>,
    instance_idx: nat,
)
    requires
        tlas_well_formed(tlas),
        all_blas_references_valid(tlas, blas_map),
        instance_idx < tlas.instances.len(),
    ensures
        blas_map.contains_key(tlas.instances[instance_idx as int].blas_id),
        blas_map[tlas.instances[instance_idx as int].blas_id].built,
{
}

///  Update mode preserves geometry count.
pub proof fn lemma_update_preserves_geometry_count(
    as_state: AccelerationStructureState,
)
    ensures
        build_as_ghost(as_state, ASBuildMode::Update).geometries.len()
            == as_state.geometries.len(),
        build_as_ghost(as_state, ASBuildMode::Update).instances.len()
            == as_state.instances.len(),
{
}

///  Building requires scratch buffer (must be in live set).
pub proof fn lemma_build_requires_scratch(
    as_state: AccelerationStructureState,
    live_buffers: Set<nat>,
)
    requires as_buffers_valid(as_state, live_buffers),
    ensures live_buffers.contains(as_state.scratch_buffer_id),
{
}

///  Well-formed AS implies all geometry buffer refs are a subset of
///  the geometry_buffer_refs set.
pub proof fn lemma_geometry_refs_subset(
    as_state: AccelerationStructureState,
    geom_idx: nat,
)
    requires
        blas_well_formed(as_state),
        geom_idx < as_state.geometries.len(),
    ensures
        as_geometry_buffer_refs(as_state).contains(
            as_state.geometries[geom_idx as int].vertex_buffer,
        ),
{
    let buf_id = as_state.geometries[geom_idx as int].vertex_buffer;
    assert(as_state.geometries[geom_idx as int].vertex_buffer == buf_id);
}

///  Building increments the generation counter.
pub proof fn lemma_build_increments_generation(
    as_state: AccelerationStructureState,
    mode: ASBuildMode,
)
    ensures
        build_as_ghost(as_state, mode).generation == as_state.generation + 1,
{
}

///  Building preserves the level.
pub proof fn lemma_build_preserves_level(
    as_state: AccelerationStructureState,
    mode: ASBuildMode,
)
    ensures
        build_as_ghost(as_state, mode).level == as_state.level,
{
}

///  Building preserves alive status.
pub proof fn lemma_build_preserves_alive(
    as_state: AccelerationStructureState,
    mode: ASBuildMode,
)
    ensures
        build_as_ghost(as_state, mode).alive == as_state.alive,
{
}

///  Destroying preserves the built flag.
pub proof fn lemma_destroy_preserves_built(
    as_state: AccelerationStructureState,
)
    ensures
        destroy_as_ghost(as_state).built == as_state.built,
{
}

///  A BLAS with all non-empty geometries and valid buffers is ready to build.
pub proof fn lemma_blas_ready_to_build(
    as_state: AccelerationStructureState,
    live_buffers: Set<nat>,
)
    requires
        blas_well_formed(as_state),
        all_geometries_non_empty(as_state),
        as_buffers_valid(as_state, live_buffers),
    ensures
        blas_well_formed(build_as_ghost(as_state, ASBuildMode::Build)),
        build_as_ghost(as_state, ASBuildMode::Build).built,
{
}

///  Building a well-formed BLAS preserves BLAS well-formedness.
pub proof fn lemma_build_preserves_blas_well_formed(
    as_state: AccelerationStructureState,
    mode: ASBuildMode,
)
    requires blas_well_formed(as_state),
    ensures blas_well_formed(build_as_ghost(as_state, mode)),
{
}

///  Building a well-formed TLAS preserves TLAS well-formedness.
pub proof fn lemma_build_preserves_tlas_well_formed(
    as_state: AccelerationStructureState,
    mode: ASBuildMode,
)
    requires tlas_well_formed(as_state),
    ensures tlas_well_formed(build_as_ghost(as_state, mode)),
{
}

///  An empty instance list means no BLAS references to validate.
pub proof fn lemma_empty_instances_trivially_valid(
    blas_map: Map<nat, AccelerationStructureState>,
)
    ensures all_blas_references_valid(
        AccelerationStructureState {
            id: 0, level: ASLevel::Top, geometries: Seq::empty(),
            instances: Seq::empty(), built: false, buffer_id: 0,
            scratch_buffer_id: 0, alive: true, generation: 0,
        },
        blas_map,
    ),
{
}

//  ── Extended Specs ──────────────────────────────────────────────────

///  Total primitive count across all geometries.
pub open spec fn as_total_primitive_count(
    as_state: AccelerationStructureState,
) -> nat
    decreases as_state.geometries.len(),
{
    if as_state.geometries.len() == 0 {
        0
    } else {
        as_state.geometries[0].primitive_count
        + as_total_primitive_count(AccelerationStructureState {
            geometries: as_state.geometries.subrange(1, as_state.geometries.len() as int),
            ..as_state
        })
    }
}

///  Maximum primitive count among all geometries.
pub open spec fn as_max_primitive_count(
    as_state: AccelerationStructureState,
) -> nat
    decreases as_state.geometries.len(),
{
    if as_state.geometries.len() == 0 {
        0
    } else {
        let rest = as_max_primitive_count(AccelerationStructureState {
            geometries: as_state.geometries.subrange(1, as_state.geometries.len() as int),
            ..as_state
        });
        if as_state.geometries[0].primitive_count >= rest {
            as_state.geometries[0].primitive_count
        } else {
            rest
        }
    }
}

///  Number of geometries in a BLAS.
pub open spec fn as_geometry_count(as_state: AccelerationStructureState) -> nat {
    as_state.geometries.len()
}

///  Number of instances in a TLAS.
pub open spec fn as_instance_count(as_state: AccelerationStructureState) -> nat {
    as_state.instances.len()
}

///  Ghost update: compact an AS (keeps all state, just marks as compact).
pub open spec fn compact_as_ghost(
    as_state: AccelerationStructureState,
) -> AccelerationStructureState
    recommends as_state.alive, as_state.built,
{
    AccelerationStructureState {
        generation: as_state.generation + 1,
        ..as_state
    }
}

///  Scratch buffer size is sufficient for the build.
pub open spec fn as_scratch_size_sufficient(
    as_state: AccelerationStructureState,
    scratch_size: nat,
) -> bool {
    scratch_size >= as_total_primitive_count(as_state)
}

///  AS is compatible with a pipeline that supports at most `max_geoms` geometries.
pub open spec fn as_compatible_with_pipeline(
    as_state: AccelerationStructureState,
    max_geoms: nat,
) -> bool {
    as_state.geometries.len() <= max_geoms
}

///  All instance custom indices are distinct.
pub open spec fn instance_custom_indices_distinct(
    tlas: AccelerationStructureState,
) -> bool {
    forall|i: nat, j: nat|
        #![trigger tlas.instances[i as int], tlas.instances[j as int]]
        i < tlas.instances.len() && j < tlas.instances.len() && i != j
        ==> tlas.instances[i as int].custom_index != tlas.instances[j as int].custom_index
}

///  All instance masks are non-zero (visible).
pub open spec fn all_instances_visible(tlas: AccelerationStructureState) -> bool {
    forall|i: nat|
        #![trigger tlas.instances[i as int]]
        i < tlas.instances.len()
        ==> tlas.instances[i as int].mask > 0
}

///  Two ASes have the same geometry structure.
pub open spec fn as_structurally_compatible(
    a: AccelerationStructureState,
    b: AccelerationStructureState,
) -> bool {
    a.level == b.level
    && a.geometries.len() == b.geometries.len()
    && a.instances.len() == b.instances.len()
}

///  An AS that has never been built.
pub open spec fn as_unbuilt(as_state: AccelerationStructureState) -> bool {
    !as_state.built && as_state.generation == 0
}

//  ── Extended Proofs ────────────────────────────────────────────────

///  A well-formed BLAS has positive geometry count.
pub proof fn lemma_blas_geometry_count_positive(as_state: AccelerationStructureState)
    requires blas_well_formed(as_state),
    ensures as_geometry_count(as_state) > 0,
{
}

///  A well-formed TLAS has positive instance count.
pub proof fn lemma_tlas_instance_count_positive(as_state: AccelerationStructureState)
    requires tlas_well_formed(as_state),
    ensures as_instance_count(as_state) > 0,
{
}

///  Compacting preserves the built flag.
pub proof fn lemma_compact_preserves_built(as_state: AccelerationStructureState)
    ensures compact_as_ghost(as_state).built == as_state.built,
{
}

///  Compacting preserves the level.
pub proof fn lemma_compact_preserves_level(as_state: AccelerationStructureState)
    ensures compact_as_ghost(as_state).level == as_state.level,
{
}

///  Compacting preserves alive status.
pub proof fn lemma_compact_preserves_alive(as_state: AccelerationStructureState)
    ensures compact_as_ghost(as_state).alive == as_state.alive,
{
}

///  Compacting increments generation.
pub proof fn lemma_compact_increments_generation(as_state: AccelerationStructureState)
    ensures compact_as_ghost(as_state).generation == as_state.generation + 1,
{
}

///  Destroying preserves the ID.
pub proof fn lemma_destroy_preserves_id(as_state: AccelerationStructureState)
    ensures destroy_as_ghost(as_state).id == as_state.id,
{
}

///  Building preserves the ID.
pub proof fn lemma_build_preserves_id(
    as_state: AccelerationStructureState,
    mode: ASBuildMode,
)
    ensures build_as_ghost(as_state, mode).id == as_state.id,
{
}

///  Building preserves buffer IDs.
pub proof fn lemma_build_preserves_buffer_ids(
    as_state: AccelerationStructureState,
    mode: ASBuildMode,
)
    ensures
        build_as_ghost(as_state, mode).buffer_id == as_state.buffer_id,
        build_as_ghost(as_state, mode).scratch_buffer_id == as_state.scratch_buffer_id,
{
}

///  Destroying preserves the geometry list.
pub proof fn lemma_destroy_preserves_geometries(as_state: AccelerationStructureState)
    ensures
        destroy_as_ghost(as_state).geometries == as_state.geometries,
        destroy_as_ghost(as_state).instances == as_state.instances,
{
}

///  A destroyed AS is not well-formed.
pub proof fn lemma_destroyed_not_well_formed(as_state: AccelerationStructureState)
    ensures !as_well_formed(destroy_as_ghost(as_state)),
{
}

///  Structural compatibility is reflexive.
pub proof fn lemma_structural_compatible_reflexive(as_state: AccelerationStructureState)
    ensures as_structurally_compatible(as_state, as_state),
{
}

///  Structural compatibility is symmetric.
pub proof fn lemma_structural_compatible_symmetric(
    a: AccelerationStructureState,
    b: AccelerationStructureState,
)
    requires as_structurally_compatible(a, b),
    ensures as_structurally_compatible(b, a),
{
}

///  Building preserves structural compatibility with the original.
pub proof fn lemma_build_preserves_structure(
    as_state: AccelerationStructureState,
    mode: ASBuildMode,
)
    ensures as_structurally_compatible(as_state, build_as_ghost(as_state, mode)),
{
}

///  Max primitive count is <= total primitive count.
pub proof fn lemma_max_primitive_leq_total(as_state: AccelerationStructureState)
    ensures as_max_primitive_count(as_state) <= as_total_primitive_count(as_state),
    decreases as_state.geometries.len(),
{
    if as_state.geometries.len() > 0 {
        let rest_state = AccelerationStructureState {
            geometries: as_state.geometries.subrange(1, as_state.geometries.len() as int),
            ..as_state
        };
        lemma_max_primitive_leq_total(rest_state);
    }
}

///  An unbuilt AS has generation 0.
pub proof fn lemma_unbuilt_generation_zero(as_state: AccelerationStructureState)
    requires as_unbuilt(as_state),
    ensures as_state.generation == 0,
{
}

///  After building, an AS is no longer unbuilt.
pub proof fn lemma_built_not_unbuilt(
    as_state: AccelerationStructureState,
    mode: ASBuildMode,
)
    ensures !as_unbuilt(build_as_ghost(as_state, mode)),
{
}

///  Compacting a well-formed BLAS preserves BLAS well-formedness.
pub proof fn lemma_compact_preserves_blas_well_formed(
    as_state: AccelerationStructureState,
)
    requires blas_well_formed(as_state),
    ensures blas_well_formed(compact_as_ghost(as_state)),
{
}

///  Compacting a well-formed TLAS preserves TLAS well-formedness.
pub proof fn lemma_compact_preserves_tlas_well_formed(
    as_state: AccelerationStructureState,
)
    requires tlas_well_formed(as_state),
    ensures tlas_well_formed(compact_as_ghost(as_state)),
{
}

} //  verus!
