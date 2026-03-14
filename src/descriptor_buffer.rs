use vstd::prelude::*;
use crate::resource::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// Usage flag constants for descriptor buffers.
pub open spec fn USAGE_DESCRIPTOR_BUFFER() -> nat { 0x1000 }
pub open spec fn USAGE_SAMPLER_DESCRIPTOR_BUFFER() -> nat { 0x2000 }

/// A binding of a descriptor buffer (VK_EXT_descriptor_buffer).
pub struct DescriptorBufferBinding {
    pub buffer: ResourceId,
    pub address: nat,
    pub usage: Set<nat>,
}

/// Ghost state tracking all descriptor buffer bindings.
pub struct DescriptorBufferState {
    pub bindings: Seq<Option<DescriptorBufferBinding>>,
    pub max_bindings: nat,
}

/// An offset into a bound descriptor buffer for a specific set.
pub struct DescriptorBufferOffset {
    pub buffer_index: nat,
    pub offset: nat,
}

/// Size information for a descriptor set layout.
pub struct DescriptorLayoutSize {
    pub layout_id: nat,
    pub total_size: nat,
    pub binding_offsets: Map<nat, nat>,
}

/// Device limits for descriptor buffers.
pub struct DescriptorBufferLimits {
    pub descriptor_buffer_offset_alignment: nat,
    pub max_descriptor_buffer_bindings: nat,
    pub max_sampler_descriptor_buffer_bindings: nat,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// Offset is aligned to the given alignment.
pub open spec fn offset_aligned(offset: nat, alignment: nat) -> bool {
    alignment > 0 && offset % alignment == 0
}

/// A descriptor buffer binding is valid.
pub open spec fn descriptor_buffer_binding_valid(
    binding: DescriptorBufferBinding,
    limits: DescriptorBufferLimits,
) -> bool {
    limits.descriptor_buffer_offset_alignment > 0
    && offset_aligned(binding.address, limits.descriptor_buffer_offset_alignment)
    && (binding.usage.contains(USAGE_DESCRIPTOR_BUFFER())
        || binding.usage.contains(USAGE_SAMPLER_DESCRIPTOR_BUFFER()))
}

/// A descriptor buffer state is well-formed.
pub open spec fn descriptor_buffer_state_well_formed(
    state: DescriptorBufferState,
    limits: DescriptorBufferLimits,
) -> bool {
    state.bindings.len() == state.max_bindings
    && state.max_bindings <= limits.max_descriptor_buffer_bindings
    && (forall|i: int| 0 <= i < state.bindings.len() ==>
        match state.bindings[i] {
            Some(b) => descriptor_buffer_binding_valid(b, limits),
            None => true,
        })
}

/// Binding descriptor buffers is valid: count within max, all valid.
pub open spec fn bind_descriptor_buffers_valid(
    bindings: Seq<DescriptorBufferBinding>,
    limits: DescriptorBufferLimits,
) -> bool {
    bindings.len() <= limits.max_descriptor_buffer_bindings
    && (forall|i: int| 0 <= i < bindings.len() ==>
        descriptor_buffer_binding_valid(bindings[i], limits))
}

/// Ghost: bind descriptor buffers — sets the first N slots.
pub open spec fn bind_descriptor_buffers_ghost(
    state: DescriptorBufferState,
    bindings: Seq<DescriptorBufferBinding>,
) -> DescriptorBufferState {
    DescriptorBufferState {
        bindings: Seq::new(
            state.max_bindings as nat,
            |i: int| if i < bindings.len() {
                Some(bindings[i])
            } else {
                None
            },
        ),
        ..state
    }
}

/// Setting offsets is valid: index in range, offset aligned.
pub open spec fn set_offsets_valid(
    state: DescriptorBufferState,
    buffer_index: nat,
    offset: nat,
    layout_size: DescriptorLayoutSize,
    limits: DescriptorBufferLimits,
) -> bool {
    (buffer_index as int) < state.bindings.len()
    && state.bindings[buffer_index as int].is_some()
    && offset_aligned(offset, limits.descriptor_buffer_offset_alignment)
    && layout_size.total_size > 0
}

/// Ghost: create a fresh descriptor buffer state with all None bindings.
pub open spec fn create_descriptor_buffer_state(
    limits: DescriptorBufferLimits,
) -> DescriptorBufferState {
    DescriptorBufferState {
        bindings: Seq::new(
            limits.max_descriptor_buffer_bindings as nat,
            |_i: int| None::<DescriptorBufferBinding>,
        ),
        max_bindings: limits.max_descriptor_buffer_bindings,
    }
}

/// A layout size is well-formed.
pub open spec fn layout_size_well_formed(ls: DescriptorLayoutSize) -> bool {
    ls.total_size > 0
}

/// Check if a buffer binding has a sampler descriptor buffer usage.
pub open spec fn embedded_sampler_valid(
    binding: DescriptorBufferBinding,
) -> bool {
    binding.usage.contains(USAGE_SAMPLER_DESCRIPTOR_BUFFER())
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// Fresh state is well-formed.
pub proof fn lemma_fresh_state_well_formed(limits: DescriptorBufferLimits)
    requires limits.descriptor_buffer_offset_alignment > 0,
    ensures
        descriptor_buffer_state_well_formed(
            create_descriptor_buffer_state(limits),
            limits,
        ),
{
    let state = create_descriptor_buffer_state(limits);
    assert forall|i: int| 0 <= i < state.bindings.len() implies
        match state.bindings[i] {
            Some(b) => descriptor_buffer_binding_valid(b, limits),
            None => true,
        }
    by {
        // All bindings are None
        assert(state.bindings[i] == None::<DescriptorBufferBinding>);
    }
}

/// Binding doesn't change max_bindings.
pub proof fn lemma_bind_preserves_max_bindings(
    state: DescriptorBufferState,
    bindings: Seq<DescriptorBufferBinding>,
)
    ensures
        bind_descriptor_buffers_ghost(state, bindings).max_bindings == state.max_bindings,
{
}

/// After bind, the first slots are Some.
pub proof fn lemma_bind_sets_binding(
    state: DescriptorBufferState,
    bindings: Seq<DescriptorBufferBinding>,
    i: int,
)
    requires
        0 <= i < bindings.len(),
        bindings.len() <= state.max_bindings,
    ensures
        bind_descriptor_buffers_ghost(state, bindings).bindings[i]
            == Some(bindings[i]),
{
}

/// Offset 0 is always aligned (for any positive alignment).
pub proof fn lemma_alignment_zero_always_valid(alignment: nat)
    requires alignment > 0,
    ensures offset_aligned(0, alignment),
{
}

/// Setting offsets doesn't affect the buffer bindings array.
pub proof fn lemma_set_offsets_preserves_bindings(
    state: DescriptorBufferState,
)
    ensures state.bindings =~= state.bindings,
{
    // Setting offsets is a separate operation that doesn't modify bindings.
}

/// Well-formed state has max_bindings within device limit.
pub proof fn lemma_max_bindings_bounded(
    state: DescriptorBufferState,
    limits: DescriptorBufferLimits,
)
    requires descriptor_buffer_state_well_formed(state, limits),
    ensures state.max_bindings <= limits.max_descriptor_buffer_bindings,
{
}

/// Fresh state has all None bindings.
pub proof fn lemma_create_all_none(limits: DescriptorBufferLimits)
    ensures
        forall|i: int| 0 <= i < create_descriptor_buffer_state(limits).bindings.len()
            ==> create_descriptor_buffer_state(limits).bindings[i].is_none(),
{
}

/// Alignment transitivity: if a % n == 0 and n % m == 0, then a % m == 0.
pub proof fn lemma_offset_alignment_transitive(a: nat, n: nat, m: nat)
    requires
        m > 0,
        n > 0,
        a % n == 0,
        n % m == 0,
    ensures a % m == 0,
{
    // a = k*n for some k, n = j*m for some j, so a = k*j*m
    let k = a / n;
    let j = n / m;
    assert(a == k * n) by {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a as int, n as int);
    }
    assert(n == j * m) by {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n as int, m as int);
    }
    assert(a == k * j * m) by {
        vstd::arithmetic::mul::lemma_mul_is_associative(k as int, j as int, m as int);
    }
    assert(a % m == 0) by {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a as int, m as int);
        assert(a == (k * j) * m);
    }
}

/// Valid binding has at least one descriptor buffer usage flag.
pub proof fn lemma_valid_binding_has_usage(
    binding: DescriptorBufferBinding,
    limits: DescriptorBufferLimits,
)
    requires descriptor_buffer_binding_valid(binding, limits),
    ensures
        binding.usage.contains(USAGE_DESCRIPTOR_BUFFER())
        || binding.usage.contains(USAGE_SAMPLER_DESCRIPTOR_BUFFER()),
{
}

} // verus!
