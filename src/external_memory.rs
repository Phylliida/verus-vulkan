use vstd::prelude::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// Handle types for external memory sharing.
pub enum ExternalMemoryHandleType {
    OpaqueFd,
    OpaqueWin32,
    DmaBuf,
    D3D11Texture,
    D3D12Heap,
    D3D12Resource,
    HostAllocation,
}

/// Properties of external memory for a given handle type.
pub struct ExternalMemoryProperties {
    /// Set of handle types compatible for sharing.
    pub compatible_handle_types: Set<ExternalMemoryHandleType>,
    /// Whether this memory can be exported.
    pub exportable: bool,
    /// Whether this memory can be imported.
    pub importable: bool,
    /// Whether a dedicated allocation is required.
    pub dedicated_only: bool,
}

/// State of an external memory allocation.
pub struct ExternalMemoryState {
    pub allocation_id: nat,
    pub handle_type: ExternalMemoryHandleType,
    pub exported: bool,
    pub imported: bool,
    pub alive: bool,
    pub size: nat,
    pub dedicated_resource: Option<nat>,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// External memory properties are valid.
pub open spec fn external_memory_properties_valid(props: ExternalMemoryProperties) -> bool {
    props.exportable || props.importable
}

/// Whether memory can be exported given its state and properties.
pub open spec fn can_export_memory(
    state: ExternalMemoryState,
    props: ExternalMemoryProperties,
) -> bool {
    state.alive
    && props.exportable
    && !state.exported
}

/// Whether memory can be imported given its state and properties.
pub open spec fn can_import_memory(
    state: ExternalMemoryState,
    props: ExternalMemoryProperties,
) -> bool {
    state.alive
    && props.importable
    && !state.imported
}

/// Ghost update: export memory.
pub open spec fn export_memory(state: ExternalMemoryState) -> ExternalMemoryState {
    ExternalMemoryState {
        exported: true,
        ..state
    }
}

/// Ghost update: import memory.
pub open spec fn import_memory(state: ExternalMemoryState) -> ExternalMemoryState {
    ExternalMemoryState {
        imported: true,
        ..state
    }
}

/// External memory is well-formed.
pub open spec fn external_memory_well_formed(state: ExternalMemoryState) -> bool {
    state.alive
    && state.size > 0
}

/// Two handle types are compatible for sharing.
pub open spec fn handle_types_compatible(
    props: ExternalMemoryProperties,
    other: ExternalMemoryHandleType,
) -> bool {
    props.compatible_handle_types.contains(other)
}

/// Whether a dedicated allocation is required for this handle type.
pub open spec fn dedicated_allocation_required(props: ExternalMemoryProperties) -> bool {
    props.dedicated_only
}

/// Ghost update: destroy external memory.
pub open spec fn destroy_external_memory(state: ExternalMemoryState) -> ExternalMemoryState {
    ExternalMemoryState {
        alive: false,
        ..state
    }
}

/// Create a fresh external memory state.
pub open spec fn create_external_memory(
    id: nat,
    handle_type: ExternalMemoryHandleType,
    size: nat,
    dedicated: Option<nat>,
) -> ExternalMemoryState {
    ExternalMemoryState {
        allocation_id: id,
        handle_type,
        exported: false,
        imported: false,
        alive: true,
        size,
        dedicated_resource: dedicated,
    }
}

// ── Lemmas ──────────────────────────────────────────────────────────────

/// Freshly created external memory is alive.
pub proof fn lemma_create_is_alive(
    id: nat, ht: ExternalMemoryHandleType, size: nat, ded: Option<nat>,
)
    ensures create_external_memory(id, ht, size, ded).alive,
{
}

/// Destroyed external memory is not alive.
pub proof fn lemma_destroy_not_alive(state: ExternalMemoryState)
    ensures !destroy_external_memory(state).alive,
{
}

/// Exported memory is still alive.
pub proof fn lemma_export_preserves_alive(state: ExternalMemoryState)
    requires state.alive,
    ensures export_memory(state).alive,
{
}

/// Imported memory is still alive.
pub proof fn lemma_import_preserves_alive(state: ExternalMemoryState)
    requires state.alive,
    ensures import_memory(state).alive,
{
}

/// Destroying preserves the allocation id.
pub proof fn lemma_destroy_preserves_id(state: ExternalMemoryState)
    ensures destroy_external_memory(state).allocation_id == state.allocation_id,
{
}

/// Export sets the exported flag.
pub proof fn lemma_export_sets_flag(state: ExternalMemoryState)
    ensures export_memory(state).exported,
{
}

} // verus!
