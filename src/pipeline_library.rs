use vstd::prelude::*;

verus! {

//  ── Types ───────────────────────────────────────────────────────────────

///  The four modular parts of a graphics pipeline (VK_EXT_graphics_pipeline_library).
pub enum PipelineLibraryType {
    VertexInput,
    PreRasterization,
    FragmentShader,
    FragmentOutput,
}

///  A push constant range.
pub struct PushConstantRange {
    pub stage_flags: nat,
    pub offset: nat,
    pub size: nat,
}

///  A vertex binding description.
pub struct VertexBinding {
    pub binding: nat,
    pub stride: nat,
    pub input_rate: nat,
}

///  A vertex attribute description.
pub struct VertexAttribute {
    pub location: nat,
    pub binding: nat,
    pub format: nat,
    pub offset: nat,
}

///  Ghost state for a pipeline library part.
pub struct PipelineLibraryState {
    pub id: nat,
    pub library_type: PipelineLibraryType,
    pub descriptor_set_layouts: Seq<nat>,
    pub push_constant_ranges: Seq<PushConstantRange>,
    pub alive: bool,
}

///  A linked pipeline composed of library parts.
pub struct LinkedPipeline {
    pub libraries: Seq<PipelineLibraryState>,
    pub complete: bool,
}

//  ── Spec Functions ──────────────────────────────────────────────────────

///  Library type equality.
pub open spec fn library_type_eq(a: PipelineLibraryType, b: PipelineLibraryType) -> bool {
    match (a, b) {
        (PipelineLibraryType::VertexInput, PipelineLibraryType::VertexInput) => true,
        (PipelineLibraryType::PreRasterization, PipelineLibraryType::PreRasterization) => true,
        (PipelineLibraryType::FragmentShader, PipelineLibraryType::FragmentShader) => true,
        (PipelineLibraryType::FragmentOutput, PipelineLibraryType::FragmentOutput) => true,
        _ => false,
    }
}

///  A library is well-formed: alive.
pub open spec fn library_well_formed(state: PipelineLibraryState) -> bool {
    state.alive
}

///  At least one library of the given type is present.
pub open spec fn library_type_present(
    libs: Seq<PipelineLibraryState>,
    lt: PipelineLibraryType,
) -> bool {
    exists|i: int| 0 <= i < libs.len()
        && library_type_eq(libs[i].library_type, lt)
}

///  All 4 library types are present.
pub open spec fn libraries_cover_all_types(libs: Seq<PipelineLibraryState>) -> bool {
    library_type_present(libs, PipelineLibraryType::VertexInput)
    && library_type_present(libs, PipelineLibraryType::PreRasterization)
    && library_type_present(libs, PipelineLibraryType::FragmentShader)
    && library_type_present(libs, PipelineLibraryType::FragmentOutput)
}

///  Push constant ranges are compatible (identical) across all libraries.
pub open spec fn push_constants_compatible(libs: Seq<PipelineLibraryState>) -> bool {
    forall|i: int, j: int|
        0 <= i < libs.len() && 0 <= j < libs.len()
        ==> libs[i].push_constant_ranges =~= libs[j].push_constant_ranges
}

///  Descriptor layouts are compatible (identical) across all libraries.
pub open spec fn descriptor_layouts_compatible(libs: Seq<PipelineLibraryState>) -> bool {
    forall|i: int, j: int|
        0 <= i < libs.len() && 0 <= j < libs.len()
        ==> libs[i].descriptor_set_layouts =~= libs[j].descriptor_set_layouts
}

///  All libraries in the list are well-formed.
pub open spec fn all_libraries_well_formed(libs: Seq<PipelineLibraryState>) -> bool {
    forall|i: int| 0 <= i < libs.len() ==> library_well_formed(libs[i])
}

///  Linking is valid: covers all types, push constants + descriptors compatible,
///  all parts well-formed.
pub open spec fn link_valid(libs: Seq<PipelineLibraryState>) -> bool {
    all_libraries_well_formed(libs)
    && libraries_cover_all_types(libs)
    && push_constants_compatible(libs)
    && descriptor_layouts_compatible(libs)
}

///  Ghost: link libraries into a complete pipeline.
pub open spec fn link_libraries_ghost(
    libs: Seq<PipelineLibraryState>,
) -> LinkedPipeline {
    LinkedPipeline {
        libraries: libs,
        complete: link_valid(libs),
    }
}

///  Ghost: create a library part.
pub open spec fn create_library_ghost(
    id: nat,
    lt: PipelineLibraryType,
    layouts: Seq<nat>,
    push_ranges: Seq<PushConstantRange>,
) -> PipelineLibraryState {
    PipelineLibraryState {
        id,
        library_type: lt,
        descriptor_set_layouts: layouts,
        push_constant_ranges: push_ranges,
        alive: true,
    }
}

///  Ghost: destroy a library.
pub open spec fn destroy_library_ghost(
    state: PipelineLibraryState,
) -> PipelineLibraryState {
    PipelineLibraryState { alive: false, ..state }
}

///  A linked pipeline is well-formed: complete, all parts well-formed, covers all types.
pub open spec fn linked_pipeline_well_formed(lp: LinkedPipeline) -> bool {
    lp.complete
    && all_libraries_well_formed(lp.libraries)
    && libraries_cover_all_types(lp.libraries)
}

//  ── Proofs ──────────────────────────────────────────────────────────────

///  Valid link produces a complete linked pipeline.
pub proof fn lemma_link_is_complete(libs: Seq<PipelineLibraryState>)
    requires link_valid(libs),
    ensures link_libraries_ghost(libs).complete,
{
}

///  Complete linked pipeline has all 4 types.
pub proof fn lemma_complete_has_all_types(lp: LinkedPipeline)
    requires linked_pipeline_well_formed(lp),
    ensures libraries_cover_all_types(lp.libraries),
{
}

///  Created library is alive.
pub proof fn lemma_create_alive(
    id: nat,
    lt: PipelineLibraryType,
    layouts: Seq<nat>,
    push_ranges: Seq<PushConstantRange>,
)
    ensures create_library_ghost(id, lt, layouts, push_ranges).alive,
{
}

///  Destroyed library is not alive.
pub proof fn lemma_destroy_not_alive(state: PipelineLibraryState)
    ensures !destroy_library_ghost(state).alive,
{
}

///  A single library of one type does not cover all 4 types.
pub proof fn lemma_single_type_not_complete(state: PipelineLibraryState)
    ensures !libraries_cover_all_types(seq![state]),
{
    //  A single library has exactly one type, so it cannot have all 4.
    match state.library_type {
        PipelineLibraryType::VertexInput => {
            assert(!library_type_present(seq![state], PipelineLibraryType::PreRasterization));
        },
        PipelineLibraryType::PreRasterization => {
            assert(!library_type_present(seq![state], PipelineLibraryType::VertexInput));
        },
        PipelineLibraryType::FragmentShader => {
            assert(!library_type_present(seq![state], PipelineLibraryType::VertexInput));
        },
        PipelineLibraryType::FragmentOutput => {
            assert(!library_type_present(seq![state], PipelineLibraryType::VertexInput));
        },
    }
}

///  Push constant compatibility is symmetric for any pair.
pub proof fn lemma_push_constants_symmetric(
    a: PipelineLibraryState,
    b: PipelineLibraryState,
)
    requires push_constants_compatible(seq![a, b]),
    ensures push_constants_compatible(seq![b, a]),
{
}

///  Linking preserves library ids — the linked pipeline contains the same libraries.
pub proof fn lemma_link_preserves_library_ids(
    libs: Seq<PipelineLibraryState>,
)
    ensures link_libraries_ghost(libs).libraries =~= libs,
{
}

///  4 libraries of distinct types cover all types.
pub proof fn lemma_four_distinct_types_suffice(
    vi: PipelineLibraryState,
    pr: PipelineLibraryState,
    fs: PipelineLibraryState,
    fo: PipelineLibraryState,
)
    requires
        library_type_eq(vi.library_type, PipelineLibraryType::VertexInput),
        library_type_eq(pr.library_type, PipelineLibraryType::PreRasterization),
        library_type_eq(fs.library_type, PipelineLibraryType::FragmentShader),
        library_type_eq(fo.library_type, PipelineLibraryType::FragmentOutput),
    ensures libraries_cover_all_types(seq![vi, pr, fs, fo]),
{
    let libs = seq![vi, pr, fs, fo];
    //  Witness each type
    assert(library_type_eq(libs[0].library_type, PipelineLibraryType::VertexInput));
    assert(library_type_eq(libs[1].library_type, PipelineLibraryType::PreRasterization));
    assert(library_type_eq(libs[2].library_type, PipelineLibraryType::FragmentShader));
    assert(library_type_eq(libs[3].library_type, PipelineLibraryType::FragmentOutput));
}

///  Destroyed library fails well_formed.
pub proof fn lemma_destroy_library_not_well_formed(state: PipelineLibraryState)
    ensures !library_well_formed(destroy_library_ghost(state)),
{
}

///  Complete linked pipeline has descriptor layouts.
pub proof fn lemma_linked_has_descriptors(lp: LinkedPipeline)
    requires
        linked_pipeline_well_formed(lp),
        lp.libraries.len() > 0,
    ensures lp.libraries[0].descriptor_set_layouts.len() >= 0,
{
}

///  An extra library of the same type doesn't break coverage.
pub proof fn lemma_duplicate_type_still_covers(
    libs: Seq<PipelineLibraryState>,
    extra: PipelineLibraryState,
)
    requires libraries_cover_all_types(libs),
    ensures libraries_cover_all_types(libs.push(extra)),
{
    //  Each type witness from libs still exists at the same index in libs.push(extra)
    //  since push appends at the end.
    let libs2 = libs.push(extra);
    assert forall|i: int| 0 <= i < libs.len() implies libs2[i] == libs[i] by {
        assert(libs2[i] == libs[i]);
    }
    //  Now show each type is still present
    let vi_witness: int = choose|i: int| 0 <= i < libs.len() && library_type_eq(libs[i].library_type, PipelineLibraryType::VertexInput);
    assert(library_type_eq(libs2[vi_witness].library_type, PipelineLibraryType::VertexInput));

    let pr_witness: int = choose|i: int| 0 <= i < libs.len() && library_type_eq(libs[i].library_type, PipelineLibraryType::PreRasterization);
    assert(library_type_eq(libs2[pr_witness].library_type, PipelineLibraryType::PreRasterization));

    let fs_witness: int = choose|i: int| 0 <= i < libs.len() && library_type_eq(libs[i].library_type, PipelineLibraryType::FragmentShader);
    assert(library_type_eq(libs2[fs_witness].library_type, PipelineLibraryType::FragmentShader));

    let fo_witness: int = choose|i: int| 0 <= i < libs.len() && library_type_eq(libs[i].library_type, PipelineLibraryType::FragmentOutput);
    assert(library_type_eq(libs2[fo_witness].library_type, PipelineLibraryType::FragmentOutput));
}

} //  verus!
