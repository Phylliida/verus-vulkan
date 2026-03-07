use vstd::prelude::*;
use crate::resource::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// Mapping from a buffer device address to the buffer it belongs to.
pub struct BufferAddressEntry {
    /// The GPU virtual address of the buffer's start.
    pub address: nat,
    /// Size of the buffer in bytes.
    pub size: nat,
    /// The resource id of the buffer.
    pub resource: ResourceId,
}

/// The complete buffer device address map.
pub struct BufferAddressMap {
    /// All registered buffer address entries.
    pub entries: Seq<BufferAddressEntry>,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// An address falls within a buffer's address range.
pub open spec fn address_in_entry(
    addr: nat,
    access_size: nat,
    entry: BufferAddressEntry,
) -> bool {
    entry.address <= addr
    && addr + access_size <= entry.address + entry.size
}

/// An address maps to a live buffer in the address map.
pub open spec fn address_maps_to_buffer(
    map: BufferAddressMap,
    addr: nat,
    access_size: nat,
) -> bool {
    exists|i: int| 0 <= i < map.entries.len()
        && address_in_entry(addr, access_size, #[trigger] map.entries[i])
}

/// Find which entry an address belongs to (if any).
pub open spec fn find_entry(
    map: BufferAddressMap,
    addr: nat,
    access_size: nat,
) -> Option<BufferAddressEntry> {
    if address_maps_to_buffer(map, addr, access_size) {
        let i = choose|i: int| 0 <= i < map.entries.len()
            && address_in_entry(addr, access_size, #[trigger] map.entries[i]);
        Some(map.entries[i])
    } else {
        None
    }
}

/// Register a new buffer's device address.
pub open spec fn register_address(
    map: BufferAddressMap,
    entry: BufferAddressEntry,
) -> BufferAddressMap {
    BufferAddressMap {
        entries: map.entries.push(entry),
    }
}

/// No two registered buffers have overlapping address ranges.
pub open spec fn no_address_overlap(map: BufferAddressMap) -> bool {
    forall|i: int, j: int|
        0 <= i < map.entries.len() && 0 <= j < map.entries.len() && i != j
        ==> !address_ranges_overlap(
            #[trigger] map.entries[i],
            #[trigger] map.entries[j],
        )
}

/// Two address entries have overlapping ranges.
pub open spec fn address_ranges_overlap(
    e1: BufferAddressEntry,
    e2: BufferAddressEntry,
) -> bool {
    e1.address < e2.address + e2.size
    && e2.address < e1.address + e1.size
}

/// All entries in the map correspond to live resources.
pub open spec fn all_addresses_live(
    map: BufferAddressMap,
    live_resources: Set<ResourceId>,
) -> bool {
    forall|i: int| 0 <= i < map.entries.len()
        ==> live_resources.contains((#[trigger] map.entries[i]).resource)
}

/// A BDA access is safe: the address maps to a live buffer.
pub open spec fn bda_access_safe(
    map: BufferAddressMap,
    addr: nat,
    access_size: nat,
    live_resources: Set<ResourceId>,
) -> bool {
    address_maps_to_buffer(map, addr, access_size)
    && all_addresses_live(map, live_resources)
}

/// An empty address map.
pub open spec fn empty_address_map() -> BufferAddressMap {
    BufferAddressMap { entries: Seq::empty() }
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// An empty address map has no overlaps.
pub proof fn lemma_empty_map_no_overlap()
    ensures no_address_overlap(empty_address_map()),
{
}

/// After registering a buffer, its address maps to it.
pub proof fn lemma_register_maps_address(
    map: BufferAddressMap,
    entry: BufferAddressEntry,
    addr: nat,
    access_size: nat,
)
    requires address_in_entry(addr, access_size, entry),
    ensures
        address_maps_to_buffer(register_address(map, entry), addr, access_size),
{
    let new_map = register_address(map, entry);
    let i = (new_map.entries.len() - 1) as int;
    assert(new_map.entries[i] == entry);
    assert(address_in_entry(addr, access_size, new_map.entries[i]));
}

/// Registering preserves existing mappings.
pub proof fn lemma_register_preserves_mappings(
    map: BufferAddressMap,
    entry: BufferAddressEntry,
    addr: nat,
    access_size: nat,
)
    requires address_maps_to_buffer(map, addr, access_size),
    ensures
        address_maps_to_buffer(register_address(map, entry), addr, access_size),
{
    let i = choose|i: int| 0 <= i < map.entries.len()
        && address_in_entry(addr, access_size, #[trigger] map.entries[i]);
    let new_map = register_address(map, entry);
    assert(new_map.entries[i] == map.entries[i]);
}

/// bda_access_safe implies the address maps to some buffer.
pub proof fn lemma_safe_implies_mapped(
    map: BufferAddressMap,
    addr: nat,
    access_size: nat,
    live_resources: Set<ResourceId>,
)
    requires bda_access_safe(map, addr, access_size, live_resources),
    ensures address_maps_to_buffer(map, addr, access_size),
{
}

/// An empty map trivially has all addresses live (vacuously true).
pub proof fn lemma_empty_map_all_live(live_resources: Set<ResourceId>)
    ensures all_addresses_live(empty_address_map(), live_resources),
{
}

/// An address within a buffer's range is in-bounds.
pub proof fn lemma_address_in_bounds(
    entry: BufferAddressEntry,
    addr: nat,
    access_size: nat,
)
    requires address_in_entry(addr, access_size, entry),
    ensures
        addr >= entry.address,
        addr + access_size <= entry.address + entry.size,
{
}

} // verus!
