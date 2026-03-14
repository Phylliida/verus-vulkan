use vstd::prelude::*;
use crate::resource::*;

verus! {

// ── Memory Domains ─────────────────────────────────────────────────────
//
// Models the Vulkan memory model's domain system.
// The GPU and CPU each have their own memory domain. Data written in one
// domain must be made "available" and then "visible" in the other domain
// before it can be read correctly.

/// A memory domain in the Vulkan memory model.
pub enum MemoryDomain {
    /// Device domain: GPU caches and VRAM.
    Device,
    /// Host domain: CPU caches and system RAM.
    Host,
}

/// Memory visibility state for a resource in a specific domain.
pub enum VisibilityState {
    /// Data has been written but not yet made available.
    /// Other agents in ANY domain cannot see the latest writes.
    Written,
    /// Data has been made available (flushed from writer's caches)
    /// but not yet visible in the target domain.
    Available,
    /// Data is visible in this domain and can be read correctly.
    Visible,
}

/// Per-resource, per-domain memory state.
pub struct DomainState {
    /// Which domain this state tracks.
    pub domain: MemoryDomain,
    /// Current visibility state.
    pub visibility: VisibilityState,
}

/// Full memory coherence state for a resource.
pub struct MemoryCoherenceState {
    /// The resource being tracked.
    pub resource: ResourceId,
    /// State in the device domain.
    pub device: DomainState,
    /// State in the host domain.
    pub host: DomainState,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// Create initial coherence state for a resource (both domains visible).
pub open spec fn initial_coherence(resource: ResourceId) -> MemoryCoherenceState {
    MemoryCoherenceState {
        resource,
        device: DomainState {
            domain: MemoryDomain::Device,
            visibility: VisibilityState::Visible,
        },
        host: DomainState {
            domain: MemoryDomain::Host,
            visibility: VisibilityState::Visible,
        },
    }
}

/// After a GPU write: device domain goes to Written, host domain invalidated.
pub open spec fn gpu_write(state: MemoryCoherenceState) -> MemoryCoherenceState {
    MemoryCoherenceState {
        device: DomainState {
            visibility: VisibilityState::Written,
            ..state.device
        },
        host: DomainState {
            visibility: VisibilityState::Written,
            ..state.host
        },
        ..state
    }
}

/// After a CPU write: host domain goes to Written, device domain invalidated.
pub open spec fn cpu_write(state: MemoryCoherenceState) -> MemoryCoherenceState {
    MemoryCoherenceState {
        device: DomainState {
            visibility: VisibilityState::Written,
            ..state.device
        },
        host: DomainState {
            visibility: VisibilityState::Written,
            ..state.host
        },
        ..state
    }
}

/// Make available: flush writer's caches (Written → Available in writer's domain).
pub open spec fn make_available(
    state: MemoryCoherenceState,
    domain: MemoryDomain,
) -> MemoryCoherenceState {
    match domain {
        MemoryDomain::Device => MemoryCoherenceState {
            device: DomainState {
                visibility: VisibilityState::Available,
                ..state.device
            },
            ..state
        },
        MemoryDomain::Host => MemoryCoherenceState {
            host: DomainState {
                visibility: VisibilityState::Available,
                ..state.host
            },
            ..state
        },
    }
}

/// Make visible: invalidate reader's caches (Available → Visible in reader's domain).
pub open spec fn make_visible(
    state: MemoryCoherenceState,
    domain: MemoryDomain,
) -> MemoryCoherenceState {
    match domain {
        MemoryDomain::Device => MemoryCoherenceState {
            device: DomainState {
                visibility: VisibilityState::Visible,
                ..state.device
            },
            ..state
        },
        MemoryDomain::Host => MemoryCoherenceState {
            host: DomainState {
                visibility: VisibilityState::Visible,
                ..state.host
            },
            ..state
        },
    }
}

/// A resource is readable in a domain if it's Visible there.
pub open spec fn readable_in_domain(
    state: MemoryCoherenceState,
    domain: MemoryDomain,
) -> bool {
    match domain {
        MemoryDomain::Device => state.device.visibility is Visible,
        MemoryDomain::Host => state.host.visibility is Visible,
    }
}

/// A full barrier: make available in writer's domain, then visible in reader's domain.
pub open spec fn full_barrier(
    state: MemoryCoherenceState,
    writer_domain: MemoryDomain,
    reader_domain: MemoryDomain,
) -> MemoryCoherenceState {
    make_visible(make_available(state, writer_domain), reader_domain)
}

/// Whether coherent memory (host-visible + host-coherent) needs explicit barriers.
/// Coherent memory is always visible in both domains — no barriers needed.
pub open spec fn is_coherent_memory(state: MemoryCoherenceState) -> bool {
    state.device.visibility is Visible
    && state.host.visibility is Visible
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// Initial state is coherent.
pub proof fn lemma_initial_is_coherent(resource: ResourceId)
    ensures is_coherent_memory(initial_coherence(resource)),
{
}

/// Initial state is readable in both domains.
pub proof fn lemma_initial_readable_both(resource: ResourceId)
    ensures
        readable_in_domain(initial_coherence(resource), MemoryDomain::Device),
        readable_in_domain(initial_coherence(resource), MemoryDomain::Host),
{
}

/// After a GPU write, the resource is not directly readable by the host.
pub proof fn lemma_gpu_write_invalidates_host(state: MemoryCoherenceState)
    ensures !readable_in_domain(gpu_write(state), MemoryDomain::Host),
{
}

/// After a CPU write, the resource is not directly readable by the device.
pub proof fn lemma_cpu_write_invalidates_device(state: MemoryCoherenceState)
    ensures !readable_in_domain(cpu_write(state), MemoryDomain::Device),
{
}

/// A full barrier after a GPU write makes the resource readable by the host.
pub proof fn lemma_gpu_write_barrier_host_read(state: MemoryCoherenceState)
    ensures readable_in_domain(
        full_barrier(gpu_write(state), MemoryDomain::Device, MemoryDomain::Host),
        MemoryDomain::Host,
    ),
{
}

/// A full barrier after a CPU write makes the resource readable by the device.
pub proof fn lemma_cpu_write_barrier_device_read(state: MemoryCoherenceState)
    ensures readable_in_domain(
        full_barrier(cpu_write(state), MemoryDomain::Host, MemoryDomain::Device),
        MemoryDomain::Device,
    ),
{
}

/// Make available preserves the other domain's state.
pub proof fn lemma_make_available_preserves_other(
    state: MemoryCoherenceState,
    domain: MemoryDomain,
)
    ensures
        match domain {
            MemoryDomain::Device => make_available(state, domain).host == state.host,
            MemoryDomain::Host => make_available(state, domain).device == state.device,
        },
{
}

/// Make visible preserves the other domain's state.
pub proof fn lemma_make_visible_preserves_other(
    state: MemoryCoherenceState,
    domain: MemoryDomain,
)
    ensures
        match domain {
            MemoryDomain::Device => make_visible(state, domain).host == state.host,
            MemoryDomain::Host => make_visible(state, domain).device == state.device,
        },
{
}

/// After GPU write + device-domain available + device-domain visible,
/// the GPU can read its own writes.
pub proof fn lemma_gpu_self_read_after_barrier(state: MemoryCoherenceState)
    ensures readable_in_domain(
        full_barrier(gpu_write(state), MemoryDomain::Device, MemoryDomain::Device),
        MemoryDomain::Device,
    ),
{
}

} // verus!
