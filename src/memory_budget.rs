use vstd::prelude::*;
use crate::device::*;
use crate::resource::*;
use crate::lifetime::*;

verus! {

// ── Spec Functions ──────────────────────────────────────────────────────

/// A full allocation+binding cycle: allocate on the correct heap and
/// increment the live buffer count.
pub open spec fn allocate_and_create_buffer(
    dev: DeviceState,
    heap_idx: nat,
    size: nat,
) -> DeviceState {
    create_buffer_ghost(allocate_memory_ghost(dev, heap_idx, size))
}

/// A full destroy+free cycle: decrement the live buffer count and
/// free the memory.
pub open spec fn destroy_and_free_buffer(
    dev: DeviceState,
    heap_idx: nat,
    size: nat,
) -> DeviceState {
    free_memory_ghost(destroy_buffer_ghost(dev), heap_idx, size)
}

/// A full allocation+creation cycle for images.
pub open spec fn allocate_and_create_image(
    dev: DeviceState,
    heap_idx: nat,
    size: nat,
) -> DeviceState {
    create_image_ghost(allocate_memory_ghost(dev, heap_idx, size))
}

/// A full destroy+free cycle for images.
pub open spec fn destroy_and_free_image(
    dev: DeviceState,
    heap_idx: nat,
    size: nat,
) -> DeviceState {
    free_memory_ghost(destroy_image_ghost(dev), heap_idx, size)
}

/// After N identical allocations, the heap usage increases by N*size.
pub open spec fn n_allocations(
    dev: DeviceState,
    heap_idx: nat,
    size: nat,
    count: nat,
) -> DeviceState
    decreases count,
{
    if count == 0 {
        dev
    } else {
        allocate_memory_ghost(
            n_allocations(dev, heap_idx, size, (count - 1) as nat),
            heap_idx,
            size,
        )
    }
}

// ── Proofs ──────────────────────────────────────────────────────────────

/// Allocating then freeing the same amount restores the original heap usage.
pub proof fn lemma_alloc_free_roundtrip(
    dev: DeviceState,
    heap_idx: nat,
    size: nat,
)
    requires
        device_well_formed(dev),
        heap_fits(dev, heap_idx, size),
    ensures
        free_memory_ghost(allocate_memory_ghost(dev, heap_idx, size), heap_idx, size)
            .heap_usage[heap_idx] == dev.heap_usage[heap_idx],
{
    let after_alloc = allocate_memory_ghost(dev, heap_idx, size);
    assert(after_alloc.heap_usage[heap_idx] == dev.heap_usage[heap_idx] + size);
}

/// Creating and destroying a buffer returns live_buffers to its original value.
pub proof fn lemma_create_destroy_buffer_roundtrip(dev: DeviceState)
    ensures
        destroy_buffer_ghost(create_buffer_ghost(dev)).live_buffers == dev.live_buffers,
{
    let after_create = create_buffer_ghost(dev);
    assert(after_create.live_buffers == dev.live_buffers + 1);
    assert(after_create.live_buffers > 0);
}

/// Creating and destroying an image returns live_images to its original value.
pub proof fn lemma_create_destroy_image_roundtrip(dev: DeviceState)
    ensures
        destroy_image_ghost(create_image_ghost(dev)).live_images == dev.live_images,
{
    let after_create = create_image_ghost(dev);
    assert(after_create.live_images == dev.live_images + 1);
}

/// The full allocate+create then destroy+free buffer roundtrip preserves well-formedness.
pub proof fn lemma_buffer_lifecycle_preserves_well_formed(
    dev: DeviceState,
    heap_idx: nat,
    size: nat,
)
    requires
        device_well_formed(dev),
        heap_fits(dev, heap_idx, size),
    ensures
        device_well_formed(
            destroy_and_free_buffer(
                allocate_and_create_buffer(dev, heap_idx, size),
                heap_idx,
                size,
            )
        ),
{
    let after_alloc_create = allocate_and_create_buffer(dev, heap_idx, size);
    // alloc preserves well-formed
    lemma_allocate_preserves_well_formed(dev, heap_idx, size);
    let after_alloc = allocate_memory_ghost(dev, heap_idx, size);
    // create_buffer_ghost doesn't touch heaps
    assert(after_alloc_create.heap_usage =~= after_alloc.heap_usage);
    assert(after_alloc_create.heap_capacity =~= after_alloc.heap_capacity);
    assert(after_alloc_create.num_heaps == after_alloc.num_heaps);
    assert(after_alloc_create.memory_type_to_heap =~= after_alloc.memory_type_to_heap);
    assert(after_alloc_create.num_memory_types == after_alloc.num_memory_types);
    assert(device_well_formed(after_alloc_create));

    // destroy_buffer_ghost doesn't touch heaps either
    let after_destroy = destroy_buffer_ghost(after_alloc_create);
    assert(after_destroy.heap_usage =~= after_alloc_create.heap_usage);
    assert(device_well_formed(after_destroy));

    // free restores budget
    lemma_free_restores_budget(after_destroy, heap_idx, size);
}

/// Allocating within budget leaves room for future allocations of the remainder.
pub proof fn lemma_partial_allocation_leaves_room(
    dev: DeviceState,
    heap_idx: nat,
    first_size: nat,
    second_size: nat,
)
    requires
        device_well_formed(dev),
        heap_fits(dev, heap_idx, first_size + second_size),
    ensures
        heap_fits(allocate_memory_ghost(dev, heap_idx, first_size), heap_idx, second_size),
{
    let after_first = allocate_memory_ghost(dev, heap_idx, first_size);
    assert(after_first.heap_usage[heap_idx] == dev.heap_usage[heap_idx] + first_size);
}

/// Two sequential allocations on the same heap sum their usage.
pub proof fn lemma_sequential_allocations_sum(
    dev: DeviceState,
    heap_idx: nat,
    size1: nat,
    size2: nat,
)
    requires
        device_well_formed(dev),
        heap_fits(dev, heap_idx, size1 + size2),
    ensures ({
        let dev1 = allocate_memory_ghost(dev, heap_idx, size1);
        let dev2 = allocate_memory_ghost(dev1, heap_idx, size2);
        dev2.heap_usage[heap_idx] == dev.heap_usage[heap_idx] + size1 + size2
    }),
{
    let dev1 = allocate_memory_ghost(dev, heap_idx, size1);
    assert(dev1.heap_usage[heap_idx] == dev.heap_usage[heap_idx] + size1);
    let dev2 = allocate_memory_ghost(dev1, heap_idx, size2);
    assert(dev2.heap_usage[heap_idx] == dev1.heap_usage[heap_idx] + size2);
}

/// Allocating on one heap does not affect another heap's usage.
pub proof fn lemma_allocation_independent_heaps(
    dev: DeviceState,
    heap_a: nat,
    heap_b: nat,
    size: nat,
)
    requires
        device_well_formed(dev),
        heap_fits(dev, heap_a, size),
        heap_a != heap_b,
        heap_b < dev.num_heaps,
    ensures
        allocate_memory_ghost(dev, heap_a, size).heap_usage[heap_b]
            == dev.heap_usage[heap_b],
{
}

/// Freeing on one heap does not affect another heap's usage.
pub proof fn lemma_free_independent_heaps(
    dev: DeviceState,
    heap_a: nat,
    heap_b: nat,
    size: nat,
)
    requires
        device_well_formed(dev),
        heap_a < dev.num_heaps,
        heap_b < dev.num_heaps,
        heap_a != heap_b,
        size <= dev.heap_usage[heap_a],
    ensures
        free_memory_ghost(dev, heap_a, size).heap_usage[heap_b]
            == dev.heap_usage[heap_b],
{
}

/// Creating/destroying buffers does not affect heap usage at all.
pub proof fn lemma_buffer_lifecycle_no_heap_effect(
    dev: DeviceState,
    heap_idx: nat,
)
    requires
        heap_idx < dev.num_heaps,
        dev.heap_usage.contains_key(heap_idx),
    ensures
        create_buffer_ghost(dev).heap_usage[heap_idx] == dev.heap_usage[heap_idx],
        destroy_buffer_ghost(dev).heap_usage[heap_idx] == dev.heap_usage[heap_idx],
{
}

/// A device with zero live resources after freeing all memory is ready for shutdown.
pub proof fn lemma_clean_shutdown_after_full_free(
    dev: DeviceState,
)
    requires
        dev.live_buffers == 0,
        dev.live_images == 0,
        dev.live_pipelines == 0,
        dev.live_descriptor_pools == 0,
        dev.pending_submissions.len() == 0,
    ensures
        device_ready_for_shutdown(dev),
{
}

/// N allocations of `size` bytes increase heap usage by exactly N*size.
pub proof fn lemma_n_allocations_sum(
    dev: DeviceState,
    heap_idx: nat,
    size: nat,
    count: nat,
)
    requires
        device_well_formed(dev),
        heap_fits(dev, heap_idx, count * size),
    ensures
        n_allocations(dev, heap_idx, size, count).heap_usage.contains_key(heap_idx),
        n_allocations(dev, heap_idx, size, count).heap_usage[heap_idx]
            == dev.heap_usage[heap_idx] + count * size,
    decreases count,
{
    if count == 0 {
        assert(count * size == 0) by(nonlinear_arith)
            requires count == 0nat;
    } else {
        let pc: nat = (count - 1) as nat;

        // Arithmetic: count * size == pc * size + size
        assert(count * size == pc * size + size) by(nonlinear_arith)
            requires count == pc + 1;

        // pc * size fits in the heap
        assert(pc * size <= count * size);
        assert(heap_fits(dev, heap_idx, pc * size));

        // Inductive hypothesis: after pc allocations, usage == base + pc*size
        lemma_n_allocations_sum(dev, heap_idx, size, pc);

        // The pc-th result's heap usage
        let base = dev.heap_usage[heap_idx];
        let pc_usage = n_allocations(dev, heap_idx, size, pc).heap_usage[heap_idx];
        assert(pc_usage == base + pc * size);

        // Explicitly unfold: n_allocations(_, _, _, count) == allocate_memory_ghost(n_allocations(_, _, _, pc), _, _)
        let prev_dev = n_allocations(dev, heap_idx, size, pc);
        let full_dev = n_allocations(dev, heap_idx, size, count);
        assert(full_dev == allocate_memory_ghost(prev_dev, heap_idx, size));
        assert(full_dev.heap_usage == prev_dev.heap_usage.insert(heap_idx, prev_dev.heap_usage[heap_idx] + size));
        assert(full_dev.heap_usage.contains_key(heap_idx));
        assert(full_dev.heap_usage[heap_idx] == prev_dev.heap_usage[heap_idx] + size);
        assert(full_dev.heap_usage[heap_idx] == base + pc * size + size);

        // Chain to count * size
        assert(base + pc * size + size == base + count * size) by(nonlinear_arith)
            requires count == pc + 1;
        // Explicitly match postcondition
        assert(full_dev.heap_usage[heap_idx] == dev.heap_usage[heap_idx] + count * size);
        assert(n_allocations(dev, heap_idx, size, count).heap_usage[heap_idx]
            == dev.heap_usage[heap_idx] + count * size);
    }
}

} // verus!
