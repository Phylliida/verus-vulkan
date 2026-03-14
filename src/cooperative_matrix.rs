use vstd::prelude::*;
use crate::flags::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// Cooperative matrix element type (VK_KHR_cooperative_matrix).
pub enum CooperativeMatrixType {
    Float16,
    Float32,
    Int8,
    Int32,
}

/// Properties describing a cooperative matrix multiply configuration.
pub struct CooperativeMatrixProperties {
    pub m_size: nat,
    pub n_size: nat,
    pub k_size: nat,
    pub a_type: CooperativeMatrixType,
    pub b_type: CooperativeMatrixType,
    pub c_type: CooperativeMatrixType,
    pub result_type: CooperativeMatrixType,
    pub saturating_accumulation: bool,
}

/// Device limits for cooperative matrix operations.
pub struct CooperativeMatrixLimits {
    pub supported_stages: Set<nat>,
    pub max_workgroup_properties: Seq<CooperativeMatrixProperties>,
}

/// Parameters for a cooperative matrix dispatch.
pub struct CooperativeMatrixDispatch {
    pub properties: CooperativeMatrixProperties,
    pub workgroup_x: nat,
    pub workgroup_y: nat,
    pub workgroup_z: nat,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// Cooperative matrix properties are well-formed: m,n,k > 0.
pub open spec fn cooperative_matrix_properties_well_formed(
    props: CooperativeMatrixProperties,
) -> bool {
    props.m_size > 0
    && props.n_size > 0
    && props.k_size > 0
}

/// Cooperative matrix limits are well-formed.
pub open spec fn cooperative_matrix_limits_well_formed(
    limits: CooperativeMatrixLimits,
) -> bool {
    limits.supported_stages.contains(STAGE_COMPUTE_SHADER())
    && limits.max_workgroup_properties.len() > 0
    && (forall|i: int| 0 <= i < limits.max_workgroup_properties.len() ==>
        cooperative_matrix_properties_well_formed(limits.max_workgroup_properties[i]))
}

/// Properties are in the device's supported list.
pub open spec fn cooperative_matrix_supported(
    limits: CooperativeMatrixLimits,
    props: CooperativeMatrixProperties,
) -> bool {
    exists|i: int| 0 <= i < limits.max_workgroup_properties.len()
        && limits.max_workgroup_properties[i] == props
}

/// A cooperative matrix dispatch is valid.
pub open spec fn cooperative_matrix_dispatch_valid(
    dispatch: CooperativeMatrixDispatch,
    limits: CooperativeMatrixLimits,
) -> bool {
    cooperative_matrix_supported(limits, dispatch.properties)
    && dispatch.workgroup_x > 0
    && dispatch.workgroup_y > 0
    && dispatch.workgroup_z > 0
}

/// Output tile size: m * n elements.
pub open spec fn matrix_multiply_output_elements(
    props: CooperativeMatrixProperties,
) -> nat {
    props.m_size * props.n_size
}

/// Input elements: A is m×k, B is k×n.
pub open spec fn matrix_multiply_input_elements(
    props: CooperativeMatrixProperties,
) -> nat {
    props.m_size * props.k_size + props.k_size * props.n_size
}

/// Size in bytes for a matrix element type.
pub open spec fn matrix_type_size_bytes(mt: CooperativeMatrixType) -> nat {
    match mt {
        CooperativeMatrixType::Float16 => 2,
        CooperativeMatrixType::Float32 => 4,
        CooperativeMatrixType::Int8 => 1,
        CooperativeMatrixType::Int32 => 4,
    }
}

/// Memory needed per workgroup for a cooperative matrix operation.
pub open spec fn cooperative_matrix_workgroup_memory(
    props: CooperativeMatrixProperties,
) -> nat {
    props.m_size * props.k_size * matrix_type_size_bytes(props.a_type)
    + props.k_size * props.n_size * matrix_type_size_bytes(props.b_type)
    + props.m_size * props.n_size * matrix_type_size_bytes(props.c_type)
}

/// Whether the cooperative matrix types are compatible.
pub open spec fn cooperative_matrix_types_compatible(
    props: CooperativeMatrixProperties,
) -> bool {
    props.result_type == props.c_type
}

/// Total workgroups in a dispatch.
pub open spec fn total_cooperative_workgroups(
    dispatch: CooperativeMatrixDispatch,
) -> nat {
    dispatch.workgroup_x * dispatch.workgroup_y * dispatch.workgroup_z
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// Well-formed properties have positive dimensions.
pub proof fn lemma_well_formed_positive_dimensions(props: CooperativeMatrixProperties)
    requires cooperative_matrix_properties_well_formed(props),
    ensures props.m_size > 0 && props.n_size > 0 && props.k_size > 0,
{
}

/// Well-formed properties yield positive output element count.
pub proof fn lemma_output_elements_positive(props: CooperativeMatrixProperties)
    requires cooperative_matrix_properties_well_formed(props),
    ensures matrix_multiply_output_elements(props) > 0,
{
    vstd::arithmetic::mul::lemma_mul_strictly_positive(
        props.m_size as int,
        props.n_size as int,
    );
}

/// Valid dispatch implies properties are in the supported list.
pub proof fn lemma_supported_in_limits(
    dispatch: CooperativeMatrixDispatch,
    limits: CooperativeMatrixLimits,
)
    requires cooperative_matrix_dispatch_valid(dispatch, limits),
    ensures cooperative_matrix_supported(limits, dispatch.properties),
{
}

/// Well-formed limits have compute stage supported.
pub proof fn lemma_compute_stage_required(limits: CooperativeMatrixLimits)
    requires cooperative_matrix_limits_well_formed(limits),
    ensures limits.supported_stages.contains(STAGE_COMPUTE_SHADER()),
{
}

/// For k > 1, input elements exceed m + n (grows linearly with k).
pub proof fn lemma_input_larger_than_sum(props: CooperativeMatrixProperties)
    requires
        cooperative_matrix_properties_well_formed(props),
        props.k_size > 1,
    ensures matrix_multiply_input_elements(props) > props.m_size + props.n_size,
{
    let m = props.m_size;
    let n = props.n_size;
    let k = props.k_size;
    // m*k >= 2*m since k >= 2, and k*n >= 2*n since k >= 2
    vstd::arithmetic::mul::lemma_mul_inequality(2, k as int, m as int);
    vstd::arithmetic::mul::lemma_mul_inequality(2, k as int, n as int);
}

/// Well-formed properties have positive workgroup memory.
pub proof fn lemma_workgroup_memory_positive(props: CooperativeMatrixProperties)
    requires cooperative_matrix_properties_well_formed(props),
    ensures cooperative_matrix_workgroup_memory(props) > 0,
{
    let a_size = matrix_type_size_bytes(props.a_type);
    assert(a_size > 0);
    vstd::arithmetic::mul::lemma_mul_strictly_positive(
        props.m_size as int,
        props.k_size as int,
    );
    vstd::arithmetic::mul::lemma_mul_strictly_positive(
        (props.m_size * props.k_size) as int,
        a_size as int,
    );
}

/// Valid dispatch has positive total workgroups.
pub proof fn lemma_dispatch_total_positive(
    dispatch: CooperativeMatrixDispatch,
    limits: CooperativeMatrixLimits,
)
    requires cooperative_matrix_dispatch_valid(dispatch, limits),
    ensures total_cooperative_workgroups(dispatch) > 0,
{
    vstd::arithmetic::mul::lemma_mul_strictly_positive(
        dispatch.workgroup_x as int,
        dispatch.workgroup_y as int,
    );
    vstd::arithmetic::mul::lemma_mul_strictly_positive(
        (dispatch.workgroup_x * dispatch.workgroup_y) as int,
        dispatch.workgroup_z as int,
    );
}

/// All type sizes are positive.
pub proof fn lemma_type_size_positive(mt: CooperativeMatrixType)
    ensures matrix_type_size_bytes(mt) > 0,
{
}

} // verus!
