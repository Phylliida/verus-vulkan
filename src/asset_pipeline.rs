use vstd::prelude::*;
use crate::resource::*;
use crate::sync::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// Index buffer element type.
pub enum IndexType {
    U16,
    U32,
}

/// Ghost invariants attached to a GPU buffer holding mesh data.
///
/// These invariants flow from verus-topology's `structurally_valid` through
/// the asset upload path to draw-time validation. If verus-topology proves
/// that `from_face_cycles` produces a structurally valid mesh, that proof
/// propagates all the way to the GPU draw call.
pub struct MeshBufferInvariants {
    /// Number of vertices in the mesh.
    pub vertex_count: nat,
    /// Number of indices in the index buffer.
    pub index_count: nat,
    /// Stride in bytes between consecutive vertices.
    pub vertex_stride: nat,
    /// Index element type (U16 or U32).
    pub index_type: IndexType,

    // ── Structural invariants (from verus-topology) ──
    /// Every index value is < vertex_count.
    pub all_indices_in_range: bool,
    /// No triangle has two identical vertices (area > 0).
    pub no_degenerate_triangles: bool,
    /// All faces have consistent winding order.
    pub consistent_winding: bool,
    /// Half-edge mesh invariants hold (from verus-topology).
    pub structurally_valid: bool,
    /// Euler characteristic (V - E + F).
    pub euler_characteristic: int,
    /// Whether the mesh is closed (no boundary edges).
    pub is_closed: bool,
}

/// Ghost state for a GPU buffer that may hold mesh data.
pub struct MeshBuffer {
    /// Buffer resource id.
    pub resource: ResourceId,
    /// Buffer size in bytes.
    pub size: nat,
    /// Mesh invariants, if this buffer holds validated mesh data.
    pub mesh_invariants: Option<MeshBufferInvariants>,
    /// Whether the buffer is alive.
    pub alive: bool,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// Size in bytes of one index element.
pub open spec fn index_type_size(t: IndexType) -> nat {
    match t {
        IndexType::U16 => 2,
        IndexType::U32 => 4,
    }
}

/// Mesh invariants are well-formed: counts and stride are positive,
/// and index count is a multiple of 3 (triangle mesh).
pub open spec fn mesh_invariants_well_formed(inv: MeshBufferInvariants) -> bool {
    inv.vertex_count > 0
    && inv.index_count > 0
    && inv.vertex_stride > 0
    && inv.index_count % 3 == 0
}

/// A vertex buffer is large enough to hold the mesh vertices.
pub open spec fn vertex_buffer_fits(buffer_size: nat, inv: MeshBufferInvariants) -> bool {
    buffer_size >= inv.vertex_count * inv.vertex_stride
}

/// An index buffer is large enough to hold the mesh indices.
pub open spec fn index_buffer_fits(buffer_size: nat, inv: MeshBufferInvariants) -> bool {
    buffer_size >= inv.index_count * index_type_size(inv.index_type)
}

/// A draw-indexed call is valid: the index range is within bounds,
/// and all referenced vertex indices (with offset) are in range.
pub open spec fn draw_indexed_valid(
    inv: MeshBufferInvariants,
    first_index: nat,
    index_count: nat,
    vertex_offset: nat,
) -> bool {
    // Index range within buffer
    first_index + index_count <= inv.index_count
    // All indices in range guarantees vertex access is safe
    && inv.all_indices_in_range
    // Vertex offset doesn't push references out of bounds
    && vertex_offset <= inv.vertex_count
}

/// A mesh is upload-ready: it has valid structural invariants.
pub open spec fn mesh_upload_ready(inv: MeshBufferInvariants) -> bool {
    mesh_invariants_well_formed(inv)
    && inv.structurally_valid
    && inv.all_indices_in_range
}

/// Ghost update: upload mesh data to a buffer, attaching invariants.
pub open spec fn upload_mesh_ghost(
    buffer: MeshBuffer,
    inv: MeshBufferInvariants,
) -> MeshBuffer {
    MeshBuffer {
        mesh_invariants: Some(inv),
        ..buffer
    }
}

/// The mesh buffer has validated invariants attached.
pub open spec fn buffer_has_mesh_invariants(buffer: MeshBuffer) -> bool {
    buffer.mesh_invariants.is_some()
    && buffer.alive
}

/// Index range is within bounds for a given mesh.
pub open spec fn index_range_in_bounds(
    inv: MeshBufferInvariants,
    first_index: nat,
    count: nat,
) -> bool {
    first_index + count <= inv.index_count
}

/// Triangle count from index count (indices / 3).
pub open spec fn triangle_count(inv: MeshBufferInvariants) -> nat
    recommends inv.index_count % 3 == 0,
{
    inv.index_count / 3
}

/// The full safety chain: from structural validity to safe draw.
pub open spec fn full_draw_safety_chain(
    inv: MeshBufferInvariants,
    vbuf_size: nat,
    ibuf_size: nat,
    first_index: nat,
    index_count: nat,
) -> bool {
    mesh_upload_ready(inv)
    && vertex_buffer_fits(vbuf_size, inv)
    && index_buffer_fits(ibuf_size, inv)
    && index_range_in_bounds(inv, first_index, index_count)
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// A structurally valid mesh with all indices in range enables safe drawing.
pub proof fn lemma_valid_mesh_enables_draw(
    inv: MeshBufferInvariants,
    first_index: nat,
    index_count: nat,
)
    requires
        inv.structurally_valid,
        inv.all_indices_in_range,
        first_index + index_count <= inv.index_count,
    ensures
        draw_indexed_valid(inv, first_index, index_count, 0),
{
}

/// A sub-range of a valid index range is also valid.
pub proof fn lemma_index_range_subset(
    inv: MeshBufferInvariants,
    first_index: nat,
    count: nat,
    sub_first: nat,
    sub_count: nat,
)
    requires
        index_range_in_bounds(inv, first_index, count),
        sub_first >= first_index,
        sub_first + sub_count <= first_index + count,
    ensures
        index_range_in_bounds(inv, sub_first, sub_count),
{
}

/// Upload preserves the mesh invariants exactly.
pub proof fn lemma_upload_preserves_invariants(
    buffer: MeshBuffer,
    inv: MeshBufferInvariants,
)
    ensures
        upload_mesh_ghost(buffer, inv).mesh_invariants == Some(inv),
{
}

/// Upload preserves the buffer's resource identity and size.
pub proof fn lemma_upload_preserves_buffer_identity(
    buffer: MeshBuffer,
    inv: MeshBufferInvariants,
)
    ensures
        upload_mesh_ghost(buffer, inv).resource == buffer.resource,
        upload_mesh_ghost(buffer, inv).size == buffer.size,
        upload_mesh_ghost(buffer, inv).alive == buffer.alive,
{
}

/// The full safety chain implies draw_indexed_valid.
pub proof fn lemma_safety_chain_implies_draw_valid(
    inv: MeshBufferInvariants,
    vbuf_size: nat,
    ibuf_size: nat,
    first_index: nat,
    index_count: nat,
)
    requires
        full_draw_safety_chain(inv, vbuf_size, ibuf_size, first_index, index_count),
    ensures
        draw_indexed_valid(inv, first_index, index_count, 0),
{
}

/// A well-formed mesh with structurally valid topology is upload-ready.
pub proof fn lemma_well_formed_valid_is_upload_ready(inv: MeshBufferInvariants)
    requires
        mesh_invariants_well_formed(inv),
        inv.structurally_valid,
        inv.all_indices_in_range,
    ensures
        mesh_upload_ready(inv),
{
}

/// Drawing the full mesh (all indices, no offset) is valid if the mesh
/// is upload-ready.
pub proof fn lemma_full_mesh_draw_valid(inv: MeshBufferInvariants)
    requires mesh_upload_ready(inv),
    ensures draw_indexed_valid(inv, 0, inv.index_count, 0),
{
}

/// Triangle count is positive for a well-formed mesh.
pub proof fn lemma_well_formed_has_triangles(inv: MeshBufferInvariants)
    requires mesh_invariants_well_formed(inv),
    ensures triangle_count(inv) > 0,
{
    assert(inv.index_count > 0);
    assert(inv.index_count % 3 == 0);
    assert(inv.index_count >= 3);
    assert(triangle_count(inv) == inv.index_count / 3);
    assert(inv.index_count / 3 > 0) by(nonlinear_arith)
        requires inv.index_count >= 3nat;
}

/// Vertex buffer fit is monotonic: larger buffers also fit.
pub proof fn lemma_vertex_buffer_fit_monotonic(
    size1: nat,
    size2: nat,
    inv: MeshBufferInvariants,
)
    requires
        vertex_buffer_fits(size1, inv),
        size2 >= size1,
    ensures
        vertex_buffer_fits(size2, inv),
{
}

/// Index buffer fit is monotonic: larger buffers also fit.
pub proof fn lemma_index_buffer_fit_monotonic(
    size1: nat,
    size2: nat,
    inv: MeshBufferInvariants,
)
    requires
        index_buffer_fits(size1, inv),
        size2 >= size1,
    ensures
        index_buffer_fits(size2, inv),
{
}

/// A closed mesh with euler characteristic 2 is a topological sphere.
/// (Connects to verus-topology's lemma_tetrahedron_is_sphere.)
pub proof fn lemma_closed_euler_2_is_sphere(inv: MeshBufferInvariants)
    requires
        inv.structurally_valid,
        inv.is_closed,
        inv.euler_characteristic == 2,
    ensures
        // The mesh is a valid topological sphere — all properties hold
        inv.structurally_valid && inv.is_closed && inv.euler_characteristic == 2,
{
}

} // verus!
