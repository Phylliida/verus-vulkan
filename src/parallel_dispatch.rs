use vstd::prelude::*;

verus! {

// ── Types ───────────────────────────────────────────────────────────────

/// Abstract specification of a parallel kernel's write behavior.
/// Each workgroup writes to a set of buffer indices with specific values.
pub ghost struct ParallelKernelSpec {
    /// Number of workgroups dispatched.
    pub num_workgroups: nat,
    /// For workgroup wg_id, the set of buffer indices it writes.
    pub write_set: spec_fn(nat) -> Set<nat>,
    /// For workgroup wg_id and buffer index, the value written.
    pub write_value: spec_fn(nat, nat) -> int,
    /// Total buffer size.
    pub data_size: nat,
}

// ── Spec Functions ──────────────────────────────────────────────────────

/// All workgroups write to disjoint index sets.
pub open spec fn workgroups_write_disjoint(k: ParallelKernelSpec) -> bool {
    forall|w1: nat, w2: nat|
        w1 < k.num_workgroups && w2 < k.num_workgroups && w1 != w2
        ==> #[trigger] (k.write_set)(w1).disjoint((k.write_set)(w2))
}

/// All writes are in-bounds.
pub open spec fn workgroups_write_in_bounds(k: ParallelKernelSpec) -> bool {
    forall|w: nat, i: nat|
        w < k.num_workgroups && #[trigger] (k.write_set)(w).contains(i)
        ==> i < k.data_size
}

/// Apply one workgroup's writes to data: overwrite each index in write_set(wg_id).
pub open spec fn apply_workgroup(k: ParallelKernelSpec, data: Seq<int>, wg_id: nat) -> Seq<int>
    recommends data.len() == k.data_size
{
    Seq::new(data.len() as nat, |idx: int|
        if (k.write_set)(wg_id).contains(idx as nat) {
            (k.write_value)(wg_id, idx as nat)
        } else {
            data[idx]
        }
    )
}

/// Sequential execution: apply workgroups 0..n in order.
pub open spec fn sequential_result(k: ParallelKernelSpec, initial: Seq<int>, n: nat) -> Seq<int>
    decreases n,
{
    if n == 0 {
        initial
    } else {
        apply_workgroup(k, sequential_result(k, initial, (n - 1) as nat), (n - 1) as nat)
    }
}

/// Whether any workgroup writes index i.
pub open spec fn any_workgroup_writes(k: ParallelKernelSpec, i: nat) -> bool {
    exists|w: nat| w < k.num_workgroups && #[trigger] (k.write_set)(w).contains(i)
}

/// The unique workgroup that writes index i (when disjoint).
pub open spec fn writer_of(k: ParallelKernelSpec, i: nat) -> nat {
    choose|w: nat| w < k.num_workgroups && #[trigger] (k.write_set)(w).contains(i)
}

/// Parallel execution: all workgroups fire simultaneously.
/// For each index, if some workgroup writes it, use that workgroup's value;
/// otherwise keep the initial value.
pub open spec fn parallel_result(k: ParallelKernelSpec, initial: Seq<int>) -> Seq<int>
    recommends initial.len() == k.data_size, workgroups_write_disjoint(k),
{
    Seq::new(initial.len() as nat, |idx: int|
        if any_workgroup_writes(k, idx as nat) {
            (k.write_value)(writer_of(k, idx as nat), idx as nat)
        } else {
            initial[idx]
        }
    )
}

// ── Helpers ─────────────────────────────────────────────────────────────

/// sequential_result preserves buffer length.
pub proof fn lemma_sequential_result_len(k: ParallelKernelSpec, initial: Seq<int>, n: nat)
    requires initial.len() == k.data_size,
    ensures sequential_result(k, initial, n).len() == k.data_size,
    decreases n,
{
    if n > 0 {
        lemma_sequential_result_len(k, initial, (n - 1) as nat);
    }
}

/// If workgroup w < n writes index i, then sequential_result(n)[i] == write_value(w, i).
/// Key inductive lemma: disjointness ensures later workgroups don't overwrite.
pub proof fn lemma_sequential_writes_correct(
    k: ParallelKernelSpec,
    initial: Seq<int>,
    n: nat,
    w: nat,
    i: nat,
)
    requires
        workgroups_write_disjoint(k),
        workgroups_write_in_bounds(k),
        initial.len() == k.data_size,
        w < n,
        n <= k.num_workgroups,
        (k.write_set)(w).contains(i),
    ensures
        sequential_result(k, initial, n)[i as int] == (k.write_value)(w, i),
    decreases n,
{
    lemma_sequential_result_len(k, initial, (n - 1) as nat);
    let prev = sequential_result(k, initial, (n - 1) as nat);
    let step = (n - 1) as nat;
    // sequential_result(k, initial, n) == apply_workgroup(k, prev, step)
    // apply_workgroup overwrites indices in write_set(step), passes through others

    if w == step {
        // This workgroup just fired — its write is directly in apply_workgroup
        assert(apply_workgroup(k, prev, step)[i as int] == (k.write_value)(w, i));
    } else {
        // w < step (since w < n and w != n-1, so w < n-1 == step)
        assert(w < step);
        // By IH, prev[i] == write_value(w, i)
        lemma_sequential_writes_correct(k, initial, step, w, i);
        // By disjointness, step's write_set doesn't contain i
        assert((k.write_set)(w).disjoint((k.write_set)(step)));
        assert(!(k.write_set)(step).contains(i));
        // So apply_workgroup passes through: prev[i] is preserved
        assert(apply_workgroup(k, prev, step)[i as int] == prev[i as int]);
    }
}

/// If no workgroup < n writes index i, then sequential_result(n)[i] == initial[i].
pub proof fn lemma_sequential_preserves_unwritten(
    k: ParallelKernelSpec,
    initial: Seq<int>,
    n: nat,
    i: nat,
)
    requires
        workgroups_write_in_bounds(k),
        initial.len() == k.data_size,
        n <= k.num_workgroups,
        i < k.data_size,
        forall|w: nat| w < n ==> !#[trigger] (k.write_set)(w).contains(i),
    ensures
        sequential_result(k, initial, n)[i as int] == initial[i as int],
    decreases n,
{
    if n > 0 {
        let step = (n - 1) as nat;
        lemma_sequential_preserves_unwritten(k, initial, step, i);
        lemma_sequential_result_len(k, initial, step);
        let prev = sequential_result(k, initial, step);
        // step's write_set doesn't contain i
        assert(!(k.write_set)(step).contains(i));
        assert(apply_workgroup(k, prev, step)[i as int] == prev[i as int]);
    }
}

// ── Master Theorem ──────────────────────────────────────────────────────

/// Parallel execution equals sequential execution when all workgroup
/// write sets are pairwise disjoint and in-bounds.
pub proof fn lemma_parallel_equals_sequential(k: ParallelKernelSpec, initial: Seq<int>)
    requires
        workgroups_write_disjoint(k),
        workgroups_write_in_bounds(k),
        initial.len() == k.data_size,
    ensures
        parallel_result(k, initial) =~= sequential_result(k, initial, k.num_workgroups),
{
    lemma_sequential_result_len(k, initial, k.num_workgroups);
    let par = parallel_result(k, initial);
    let seq_res = sequential_result(k, initial, k.num_workgroups);

    assert(par.len() == seq_res.len());

    // Pointwise equality
    assert forall|idx: int| 0 <= idx < par.len() as int
        implies par[idx] == seq_res[idx]
    by {
        let i = idx as nat;
        if any_workgroup_writes(k, i) {
            // Some workgroup writes index i
            let w = writer_of(k, i);
            // par[idx] == write_value(w, i) by definition of parallel_result
            assert(par[idx] == (k.write_value)(w, i));
            // seq_res[idx] == write_value(w, i) by sequential_writes_correct
            lemma_sequential_writes_correct(k, initial, k.num_workgroups, w, i);
        } else {
            // No workgroup writes this index
            assert(forall|w: nat| w < k.num_workgroups ==> !#[trigger] (k.write_set)(w).contains(i));
            // par[idx] == initial[idx] by definition
            assert(par[idx] == initial[idx]);
            // seq_res[idx] == initial[idx] by preserves_unwritten
            lemma_sequential_preserves_unwritten(k, initial, k.num_workgroups, i);
        }
    }
}

/// Uniqueness: if writes are disjoint, at most one workgroup writes each index.
pub proof fn lemma_writer_unique(
    k: ParallelKernelSpec,
    w1: nat,
    w2: nat,
    i: nat,
)
    requires
        workgroups_write_disjoint(k),
        w1 < k.num_workgroups,
        w2 < k.num_workgroups,
        (k.write_set)(w1).contains(i),
        (k.write_set)(w2).contains(i),
    ensures
        w1 == w2,
{
    if w1 != w2 {
        assert((k.write_set)(w1).disjoint((k.write_set)(w2)));
        assert(false);
    }
}

} // verus!
