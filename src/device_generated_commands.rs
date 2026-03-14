use vstd::prelude::*;
use crate::flags::*;
use crate::resource::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// Token types for indirect command generation (VK_EXT_device_generated_commands).
pub enum IndirectCommandsTokenType {
    DrawToken,
    DrawIndexedToken,
    DispatchToken,
    PipelineToken,
    PushConstantToken,
    VertexBufferToken,
    IndexBufferToken,
}

/// A token within an indirect commands layout.
pub struct IndirectCommandsLayoutToken {
    pub token_type: IndirectCommandsTokenType,
    pub offset: nat,
}

/// Ghost state for an indirect commands layout.
pub struct IndirectCommandsLayoutState {
    pub id: nat,
    pub tokens: Seq<IndirectCommandsLayoutToken>,
    pub stride: nat,
    pub stage_flags: PipelineStageFlags,
    pub alive: bool,
}

/// Ghost state for an indirect execution set.
pub struct IndirectExecutionSetState {
    pub id: nat,
    pub pipeline_id: nat,
    pub max_pipelines: nat,
    pub alive: bool,
}

/// Info for a generated commands operation.
pub struct GeneratedCommandsInfo {
    pub layout_id: nat,
    pub execution_set_id: Option<nat>,
    pub preprocess_buffer: ResourceId,
    pub preprocess_size: nat,
    pub sequence_count: nat,
    pub max_sequence_count: nat,
}

/// State after preprocessing.
pub struct PreprocessState {
    pub layout_id: nat,
    pub preprocessed: bool,
    pub sequence_count: nat,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// Token size in bytes for each token type.
pub open spec fn token_size(tt: IndirectCommandsTokenType) -> nat {
    match tt {
        IndirectCommandsTokenType::DrawToken => 16,
        IndirectCommandsTokenType::DrawIndexedToken => 20,
        IndirectCommandsTokenType::DispatchToken => 12,
        IndirectCommandsTokenType::PipelineToken => 4,
        IndirectCommandsTokenType::PushConstantToken => 4,
        IndirectCommandsTokenType::VertexBufferToken => 8,
        IndirectCommandsTokenType::IndexBufferToken => 8,
    }
}

/// No two tokens overlap within the stride.
pub open spec fn tokens_non_overlapping(
    tokens: Seq<IndirectCommandsLayoutToken>,
    stride: nat,
) -> bool {
    forall|i: int, j: int|
        #![trigger tokens[i], tokens[j]]
        0 <= i < tokens.len() && 0 <= j < tokens.len() && i != j
        ==> {
            let ti = tokens[i];
            let tj = tokens[j];
            let si = token_size(ti.token_type);
            let sj = token_size(tj.token_type);
            ti.offset + si <= tj.offset || tj.offset + sj <= ti.offset
        }
}

/// Layout is well-formed: alive, tokens non-empty, stride > 0, offsets valid.
pub open spec fn layout_well_formed(state: IndirectCommandsLayoutState) -> bool {
    state.alive
    && state.tokens.len() > 0
    && state.stride > 0
    && tokens_non_overlapping(state.tokens, state.stride)
    // All tokens fit within stride
    && (forall|i: int| 0 <= i < state.tokens.len() ==>
        state.tokens[i].offset + token_size(state.tokens[i].token_type) <= state.stride)
}

/// Execution set is well-formed.
pub open spec fn execution_set_well_formed(state: IndirectExecutionSetState) -> bool {
    state.alive
    && state.max_pipelines > 0
}

/// Ghost: create a layout.
pub open spec fn create_layout_ghost(
    id: nat,
    tokens: Seq<IndirectCommandsLayoutToken>,
    stride: nat,
    stage_flags: PipelineStageFlags,
) -> IndirectCommandsLayoutState {
    IndirectCommandsLayoutState { id, tokens, stride, stage_flags, alive: true }
}

/// Ghost: destroy a layout.
pub open spec fn destroy_layout_ghost(
    state: IndirectCommandsLayoutState,
) -> IndirectCommandsLayoutState {
    IndirectCommandsLayoutState { alive: false, ..state }
}

/// Ghost: create an execution set.
pub open spec fn create_execution_set_ghost(
    id: nat,
    pipeline_id: nat,
    max_pipelines: nat,
) -> IndirectExecutionSetState {
    IndirectExecutionSetState { id, pipeline_id, max_pipelines, alive: true }
}

/// Ghost: destroy an execution set.
pub open spec fn destroy_execution_set_ghost(
    state: IndirectExecutionSetState,
) -> IndirectExecutionSetState {
    IndirectExecutionSetState { alive: false, ..state }
}

/// Preprocess is valid: buffer large enough, count within max.
pub open spec fn preprocess_valid(
    info: GeneratedCommandsInfo,
    layout: IndirectCommandsLayoutState,
    exec_set: Option<IndirectExecutionSetState>,
) -> bool {
    layout.alive
    && info.sequence_count > 0
    && info.sequence_count <= info.max_sequence_count
    && info.preprocess_size >= info.sequence_count * layout.stride
    && (match exec_set {
        Some(es) => es.alive,
        None => true,
    })
}

/// Ghost: record a preprocess operation.
pub open spec fn preprocess_ghost(info: GeneratedCommandsInfo) -> PreprocessState {
    PreprocessState {
        layout_id: info.layout_id,
        preprocessed: true,
        sequence_count: info.sequence_count,
    }
}

/// Execute is valid: preprocessed, layout matches, counts match.
pub open spec fn execute_valid(
    info: GeneratedCommandsInfo,
    preprocess: PreprocessState,
    layout: IndirectCommandsLayoutState,
) -> bool {
    preprocess.preprocessed
    && preprocess.layout_id == info.layout_id
    && preprocess.sequence_count == info.sequence_count
    && layout.alive
    && layout.id == info.layout_id
}

/// Ghost: execute consumes the preprocess state.
pub open spec fn execute_ghost(
    preprocess: PreprocessState,
) -> PreprocessState {
    PreprocessState { preprocessed: false, ..preprocess }
}

/// Minimum memory requirement for generated commands.
pub open spec fn generated_commands_memory_requirement(
    layout: IndirectCommandsLayoutState,
    max_sequences: nat,
) -> nat {
    max_sequences * layout.stride
}

/// Check if a token type is present in the layout.
pub open spec fn layout_supports_token_type(
    layout: IndirectCommandsLayoutState,
    tt: IndirectCommandsTokenType,
) -> bool {
    exists|i: int| 0 <= i < layout.tokens.len()
        && token_type_eq(layout.tokens[i].token_type, tt)
}

/// Token type equality (enums).
pub open spec fn token_type_eq(
    a: IndirectCommandsTokenType,
    b: IndirectCommandsTokenType,
) -> bool {
    match (a, b) {
        (IndirectCommandsTokenType::DrawToken, IndirectCommandsTokenType::DrawToken) => true,
        (IndirectCommandsTokenType::DrawIndexedToken, IndirectCommandsTokenType::DrawIndexedToken) => true,
        (IndirectCommandsTokenType::DispatchToken, IndirectCommandsTokenType::DispatchToken) => true,
        (IndirectCommandsTokenType::PipelineToken, IndirectCommandsTokenType::PipelineToken) => true,
        (IndirectCommandsTokenType::PushConstantToken, IndirectCommandsTokenType::PushConstantToken) => true,
        (IndirectCommandsTokenType::VertexBufferToken, IndirectCommandsTokenType::VertexBufferToken) => true,
        (IndirectCommandsTokenType::IndexBufferToken, IndirectCommandsTokenType::IndexBufferToken) => true,
        _ => false,
    }
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// Execute requires preprocessed == true.
pub proof fn lemma_preprocess_before_execute(
    info: GeneratedCommandsInfo,
    preprocess: PreprocessState,
    layout: IndirectCommandsLayoutState,
)
    requires execute_valid(info, preprocess, layout),
    ensures preprocess.preprocessed,
{
}

/// Well-formed layout has at least one token.
pub proof fn lemma_layout_has_tokens(state: IndirectCommandsLayoutState)
    requires layout_well_formed(state),
    ensures state.tokens.len() > 0,
{
}

/// Created layout is alive.
pub proof fn lemma_create_layout_alive(
    id: nat,
    tokens: Seq<IndirectCommandsLayoutToken>,
    stride: nat,
    stage_flags: PipelineStageFlags,
)
    ensures create_layout_ghost(id, tokens, stride, stage_flags).alive,
{
}

/// Destroyed layout is not alive.
pub proof fn lemma_destroy_layout_not_alive(state: IndirectCommandsLayoutState)
    ensures !destroy_layout_ghost(state).alive,
{
}

/// Created execution set is alive.
pub proof fn lemma_create_exec_set_alive(
    id: nat,
    pipeline_id: nat,
    max_pipelines: nat,
)
    ensures create_execution_set_ghost(id, pipeline_id, max_pipelines).alive,
{
}

/// Destroyed execution set is not alive.
pub proof fn lemma_destroy_exec_set_not_alive(state: IndirectExecutionSetState)
    ensures !destroy_execution_set_ghost(state).alive,
{
}

/// Preprocess ghost returns preprocessed == true.
pub proof fn lemma_preprocess_sets_preprocessed(info: GeneratedCommandsInfo)
    ensures preprocess_ghost(info).preprocessed,
{
}

/// After execute, preprocess is consumed (no longer preprocessed).
pub proof fn lemma_execute_consumes_preprocess(preprocess: PreprocessState)
    ensures !execute_ghost(preprocess).preprocessed,
{
}

/// Valid preprocess has sequence count within max.
pub proof fn lemma_sequence_count_bounded(
    info: GeneratedCommandsInfo,
    layout: IndirectCommandsLayoutState,
    exec_set: Option<IndirectExecutionSetState>,
)
    requires preprocess_valid(info, layout, exec_set),
    ensures info.sequence_count <= info.max_sequence_count,
{
}

/// Non-empty layout has positive memory requirement.
pub proof fn lemma_memory_requirement_positive(
    layout: IndirectCommandsLayoutState,
    max_sequences: nat,
)
    requires
        layout_well_formed(layout),
        max_sequences > 0,
    ensures generated_commands_memory_requirement(layout, max_sequences) > 0,
{
    vstd::arithmetic::mul::lemma_mul_strictly_positive(
        max_sequences as int,
        layout.stride as int,
    );
}

} // verus!
