use vstd::prelude::*;
use crate::parallel_dispatch::*;
use crate::compute_validation::*;
use verus_cutedsl::layout::*;
use verus_cutedsl::shape::*;
use verus_cutedsl::gemm::*;
use verus_cutedsl::predication::*;
use verus_cutedsl::runtime::gemm::gemm_int_mac;

verus! {

//  ── Types ───────────────────────────────────────────────────────────────

///  GEMM dispatch configuration: matrix dims + tile dims + grid dims.
pub ghost struct GemmDispatchConfig {
    pub m: nat,
    pub n: nat,
    pub k: nat,
    pub bm: nat,
    pub bn: nat,
    pub bk: nat,
    pub grid_x: nat,
    pub grid_y: nat,
}

///  A buffer binding for GEMM: layout + data size.
pub ghost struct GemmBufferBinding {
    pub layout: LayoutSpec,
    pub data_size: nat,
}

//  ── Spec Functions ──────────────────────────────────────────────────────

///  Grid dimensions match tile counts.
pub open spec fn grid_matches_tiles(config: &GemmDispatchConfig) -> bool {
    config.grid_x == num_tiles_ceil(config.m, config.bm)
    && config.grid_y == num_tiles_ceil(config.n, config.bn)
}

///  Linearize 2D tile coords to workgroup ID: wg_id = ti + tj * grid_x.
pub open spec fn tile_to_wg_id(ti: nat, tj: nat, grid_x: nat) -> nat {
    ti + tj * grid_x
}

///  Recover tile coords from workgroup ID.
pub open spec fn wg_id_to_ti(wg_id: nat, grid_x: nat) -> nat {
    wg_id % grid_x
}

pub open spec fn wg_id_to_tj(wg_id: nat, grid_x: nat) -> nat {
    wg_id / grid_x
}

///  Full GEMM dispatch safety: CuTe config admissible + Vulkan limits OK
///  + C buffer backing sufficient + buffers valid.
pub open spec fn gemm_dispatch_safe(
    config: &GemmDispatchConfig,
    a: &GemmBufferBinding,
    b: &GemmBufferBinding,
    c: &GemmBufferBinding,
    limits: ComputeLimits,
) -> bool {
    //  CuTe-level admissibility
    &&& gemm_config_admissible(config.m, config.n, config.k,
            config.bm, config.bn, config.bk,
            &a.layout, &b.layout, &c.layout)
    //  Shape bounds
    &&& config.m <= c.layout.shape[0]
    &&& config.n <= c.layout.shape[1]
    &&& config.m <= a.layout.shape[0]
    &&& config.k <= a.layout.shape[1]
    &&& config.k <= b.layout.shape[0]
    &&& config.n <= b.layout.shape[1]
    //  Grid matches tiles
    &&& grid_matches_tiles(config)
    //  Vulkan dispatch limits
    &&& dispatch_dimensions_valid(
            config.grid_x, config.grid_y, 1,
            limits)
    //  Tensor validity (data large enough for layout)
    &&& tensor_valid(&TensorSpec { layout: a.layout, data_size: a.data_size })
    &&& tensor_valid(&TensorSpec { layout: b.layout, data_size: b.data_size })
    &&& tensor_valid(&TensorSpec { layout: c.layout, data_size: c.data_size })
    //  Non-negative strides on C (needed for epilogue)
    &&& c.layout.non_negative_strides()
}

//  ── Write set construction for parallel framework ───────────────────────

///  Whether (ti, tj, ei, ej) represents a valid write by a workgroup.
pub open spec fn is_valid_cta_write(
    config: &GemmDispatchConfig,
    c_layout: &LayoutSpec,
    ti: nat, tj: nat, ei: nat, ej: nat,
    idx: nat,
) -> bool {
    ei < config.bm && ej < config.bn
    && epilogue_predicated_store_safe(
        config.m, config.n, ti, tj, ei, ej, config.bm, config.bn)
    && gemm_c_tile_offset(c_layout, ti, tj, ei, ej, config.bm, config.bn) >= 0
    && gemm_c_tile_offset(c_layout, ti, tj, ei, ej, config.bm, config.bn) == idx as int
}

///  The set of C buffer indices that workgroup wg_id writes.
pub open spec fn gemm_wg_write_set(
    config: &GemmDispatchConfig,
    c_layout: &LayoutSpec,
    wg_id: nat,
) -> Set<nat> {
    let ti = wg_id_to_ti(wg_id, config.grid_x);
    let tj = wg_id_to_tj(wg_id, config.grid_x);
    Set::new(|idx: nat|
        exists|ei: nat, ej: nat|
            #[trigger] is_valid_cta_write(config, c_layout, ti, tj, ei, ej, idx)
    )
}

///  The value workgroup wg_id writes to global index (gi, gj).
///  Defined directly from the global coordinates rather than recovering them.
pub open spec fn gemm_write_value_at(
    a_layout: &LayoutSpec,
    b_layout: &LayoutSpec,
    a_data: Seq<i64>,
    b_data: Seq<i64>,
    gi: nat, gj: nat, k_size: nat,
) -> int {
    gemm_int_mac(a_layout, b_layout, a_data, b_data, gi, gj, k_size)
}

///  Instantiate the parallel kernel spec for GEMM.
///  write_value is defined via choose to recover the (ei,ej) pair from the offset.
pub open spec fn gemm_as_parallel_kernel(
    config: &GemmDispatchConfig,
    c: &GemmBufferBinding,
    a_layout: &LayoutSpec,
    b_layout: &LayoutSpec,
    a_data: Seq<i64>,
    b_data: Seq<i64>,
) -> ParallelKernelSpec {
    ParallelKernelSpec {
        num_workgroups: config.grid_x * config.grid_y,
        write_set: |wg_id: nat| gemm_wg_write_set(config, &c.layout, wg_id),
        write_value: |wg_id: nat, idx: nat| {
            let ti = wg_id_to_ti(wg_id, config.grid_x);
            let tj = wg_id_to_tj(wg_id, config.grid_x);
            //  Recover tile-local coords from the C offset.
            //  The choose recovers (ei, ej) such that idx matches the offset.
            let pair = choose|pair: (nat, nat)|
                #[trigger] is_valid_cta_write(
                    config, &c.layout, ti, tj, pair.0, pair.1, idx);
            let gi = ti * config.bm + pair.0;
            let gj = tj * config.bn + pair.1;
            gemm_int_mac(a_layout, b_layout, a_data, b_data, gi, gj, config.k)
        },
        data_size: c.data_size,
    }
}

//  ── Proofs ──────────────────────────────────────────────────────────────

///  gemm_dispatch_safe implies all core CuTe correctness properties.
pub proof fn lemma_gemm_dispatch_safe_implies_correct(
    config: &GemmDispatchConfig,
    a: &GemmBufferBinding,
    b: &GemmBufferBinding,
    c: &GemmBufferBinding,
    limits: ComputeLimits,
)
    requires
        gemm_dispatch_safe(config, a, b, c, limits),
    ensures
        gemm_output_covered(config.m, config.n, config.bm, config.bn),
        k_reduction_complete(config.k, config.bk),
        gemm_output_injective(&c.layout, config.m, config.n),
        epilogue_cross_cta_disjoint(&c.layout, config.m, config.n, config.bm, config.bn),
{
    verus_cutedsl::proof::gemm_lemmas::lemma_gemm_e2e_correctness(
        config.m, config.n, config.k,
        config.bm, config.bn, config.bk,
        &a.layout, &b.layout, &c.layout,
    );
    verus_cutedsl::proof::gemm_lemmas::lemma_epilogue_cross_cta_disjoint(
        &c.layout, config.m, config.n, config.bm, config.bn,
    );
}

///  Different workgroup IDs map to different (ti, tj) pairs when grid_x > 0.
pub proof fn lemma_wg_id_to_tile_injective(
    wg_id1: nat, wg_id2: nat, grid_x: nat,
)
    requires
        grid_x > 0,
        wg_id1 != wg_id2,
    ensures
        wg_id_to_ti(wg_id1, grid_x) != wg_id_to_ti(wg_id2, grid_x)
        || wg_id_to_tj(wg_id1, grid_x) != wg_id_to_tj(wg_id2, grid_x),
{
    if wg_id_to_ti(wg_id1, grid_x) == wg_id_to_ti(wg_id2, grid_x)
        && wg_id_to_tj(wg_id1, grid_x) == wg_id_to_tj(wg_id2, grid_x)
    {
        //  Euclidean division identity: n == (n / d) * d + (n % d)
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(wg_id1 as int, grid_x as int);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(wg_id2 as int, grid_x as int);
    }
}

///  epilogue_cross_cta_disjoint implies the write sets of distinct workgroups are disjoint.
pub proof fn lemma_gemm_disjoint_bridge(
    config: &GemmDispatchConfig,
    c_layout: &LayoutSpec,
)
    requires
        config.bm > 0,
        config.bn > 0,
        config.grid_x > 0,
        c_layout.valid(),
        c_layout.rank() == 2,
        c_layout.is_injective(),
        config.m <= c_layout.shape[0],
        config.n <= c_layout.shape[1],
        grid_matches_tiles(config),
        epilogue_cross_cta_disjoint(c_layout, config.m, config.n, config.bm, config.bn),
    ensures
        forall|w1: nat, w2: nat|
            w1 < config.grid_x * config.grid_y
            && w2 < config.grid_x * config.grid_y
            && w1 != w2
            ==> #[trigger] gemm_wg_write_set(config, c_layout, w1)
                .disjoint(gemm_wg_write_set(config, c_layout, w2)),
{
    assert forall|w1: nat, w2: nat|
        w1 < config.grid_x * config.grid_y
        && w2 < config.grid_x * config.grid_y
        && w1 != w2
        implies #[trigger] gemm_wg_write_set(config, c_layout, w1)
            .disjoint(gemm_wg_write_set(config, c_layout, w2))
    by {
        let s1 = gemm_wg_write_set(config, c_layout, w1);
        let s2 = gemm_wg_write_set(config, c_layout, w2);
        let ti1 = wg_id_to_ti(w1, config.grid_x);
        let tj1 = wg_id_to_tj(w1, config.grid_x);
        let ti2 = wg_id_to_ti(w2, config.grid_x);
        let tj2 = wg_id_to_tj(w2, config.grid_x);

        //  Different wg_ids → different (ti, tj) pairs
        lemma_wg_id_to_tile_injective(w1, w2, config.grid_x);

        //  Prove disjointness by contradiction
        lemma_gemm_disjoint_bridge_inner(config, c_layout, w1, w2);
        assert(s1.disjoint(s2));
    }
}

///  Inner helper: no idx belongs to both write sets of distinct workgroups.
proof fn lemma_gemm_disjoint_bridge_inner(
    config: &GemmDispatchConfig,
    c_layout: &LayoutSpec,
    w1: nat, w2: nat,
)
    requires
        config.bm > 0,
        config.bn > 0,
        config.grid_x > 0,
        c_layout.valid(),
        c_layout.rank() == 2,
        c_layout.is_injective(),
        config.m <= c_layout.shape[0],
        config.n <= c_layout.shape[1],
        epilogue_cross_cta_disjoint(c_layout, config.m, config.n, config.bm, config.bn),
        w1 != w2,
        wg_id_to_ti(w1, config.grid_x) != wg_id_to_ti(w2, config.grid_x)
        || wg_id_to_tj(w1, config.grid_x) != wg_id_to_tj(w2, config.grid_x),
    ensures
        gemm_wg_write_set(config, c_layout, w1)
            .disjoint(gemm_wg_write_set(config, c_layout, w2)),
{
    let s1 = gemm_wg_write_set(config, c_layout, w1);
    let s2 = gemm_wg_write_set(config, c_layout, w2);
    let ti1 = wg_id_to_ti(w1, config.grid_x);
    let tj1 = wg_id_to_tj(w1, config.grid_x);
    let ti2 = wg_id_to_ti(w2, config.grid_x);
    let tj2 = wg_id_to_tj(w2, config.grid_x);

    //  Prove no index is in both write sets using C offset injectivity directly
    assert forall|idx: nat, ei1: nat, ej1: nat, ei2: nat, ej2: nat|
        #[trigger] is_valid_cta_write(config, c_layout, ti1, tj1, ei1, ej1, idx)
        && #[trigger] is_valid_cta_write(config, c_layout, ti2, tj2, ei2, ej2, idx)
        implies false
    by {
        //  From is_valid_cta_write: both offsets equal idx
        //  gemm_c_tile_offset(c, ti, tj, ei, ej, bm, bn) = gemm_c_offset(c, ti*bm+ei, tj*bn+ej)
        let gi1 = ti1 * config.bm + ei1;
        let gj1 = tj1 * config.bn + ej1;
        let gi2 = ti2 * config.bm + ei2;
        let gj2 = tj2 * config.bn + ej2;

        //  From epilogue_predicated_store_safe: gi1 < m, gj1 < n, gi2 < m, gj2 < n
        //  (ti, tj) differ, so (gi1, gj1) != (gi2, gj2)
        //  Either ti1 != ti2 => gi1 in [ti1*bm, (ti1+1)*bm), gi2 in [ti2*bm, (ti2+1)*bm) => gi1 != gi2
        //  Or tj1 != tj2 => similarly gj1 != gj2
        if ti1 != ti2 {
            if ti1 < ti2 {
                assert(gi1 < (ti1 + 1) * config.bm) by (nonlinear_arith)
                    requires ei1 < config.bm, gi1 == ti1 * config.bm + ei1;
                assert((ti1 + 1) * config.bm <= ti2 * config.bm) by (nonlinear_arith)
                    requires ti1 < ti2, config.bm > 0;
                assert(gi2 >= ti2 * config.bm) by (nonlinear_arith)
                    requires gi2 == ti2 * config.bm + ei2;
            } else {
                assert(gi2 < (ti2 + 1) * config.bm) by (nonlinear_arith)
                    requires ei2 < config.bm, gi2 == ti2 * config.bm + ei2;
                assert((ti2 + 1) * config.bm <= ti1 * config.bm) by (nonlinear_arith)
                    requires ti2 < ti1, config.bm > 0;
                assert(gi1 >= ti1 * config.bm) by (nonlinear_arith)
                    requires gi1 == ti1 * config.bm + ei1;
            }
            assert(gi1 != gi2);
        } else {
            assert(tj1 != tj2);
            if tj1 < tj2 {
                assert(gj1 < (tj1 + 1) * config.bn) by (nonlinear_arith)
                    requires ej1 < config.bn, gj1 == tj1 * config.bn + ej1;
                assert((tj1 + 1) * config.bn <= tj2 * config.bn) by (nonlinear_arith)
                    requires tj1 < tj2, config.bn > 0;
                assert(gj2 >= tj2 * config.bn) by (nonlinear_arith)
                    requires gj2 == tj2 * config.bn + ej2;
            } else {
                assert(gj2 < (tj2 + 1) * config.bn) by (nonlinear_arith)
                    requires ej2 < config.bn, gj2 == tj2 * config.bn + ej2;
                assert((tj2 + 1) * config.bn <= tj1 * config.bn) by (nonlinear_arith)
                    requires tj2 < tj1, config.bn > 0;
                assert(gj1 >= tj1 * config.bn) by (nonlinear_arith)
                    requires gj1 == tj1 * config.bn + ej1;
            }
            assert(gj1 != gj2);
        }
        assert(gi1 != gi2 || gj1 != gj2);

        //  By C layout injectivity: distinct (gi, gj) → distinct offsets
        verus_cutedsl::proof::gemm_lemmas::lemma_gemm_c_offset_injective(
            c_layout, config.m, config.n, gi1, gj1, gi2, gj2,
        );
        //  gemm_c_offset(c, gi1, gj1) != gemm_c_offset(c, gi2, gj2)
        //  But both equal idx as int — contradiction
    }

    assert forall|idx: nat| !(s1.contains(idx) && s2.contains(idx)) by {}
    assert(s1.disjoint(s2));
}

//  ── Write-in-bounds helper ────────────────────────────────────────────

///  For any valid CTA write, the target index is within the C buffer.
proof fn lemma_valid_cta_write_in_bounds(
    config: &GemmDispatchConfig,
    c: &GemmBufferBinding,
    ti: nat, tj: nat, ei: nat, ej: nat, idx: nat,
)
    requires
        config.bm > 0,
        config.bn > 0,
        c.layout.valid(),
        c.layout.rank() == 2,
        c.layout.non_negative_strides(),
        config.m <= c.layout.shape[0],
        config.n <= c.layout.shape[1],
        tensor_valid(&TensorSpec { layout: c.layout, data_size: c.data_size }),
        is_valid_cta_write(config, &c.layout, ti, tj, ei, ej, idx),
    ensures
        idx < c.data_size,
{
    let gi = ti * config.bm + ei;
    let gj = tj * config.bn + ej;
    let coords = seq![gi, gj];

    //  From epilogue_predicated_store_safe: gi < m, gj < n
    //  Combined with m <= shape[0], n <= shape[1]: coords in bounds
    assert(coords_in_bounds(coords, c.layout.shape)) by {
        assert(coords.len() == c.layout.shape.len());
        assert forall|i: int| 0 <= i < coords.len()
            implies #[trigger] coords[i] < c.layout.shape[i]
        by {
            if i == 0 { assert(gi < config.m); }
            else { assert(gj < config.n); }
        }
    }

    //  linearize in bounds → offset < cosize ≤ data_size
    verus_cutedsl::proof::shape_lemmas::lemma_linearize_bound(coords, c.layout.shape);
    let lin = linearize(coords, c.layout.shape);
    verus_cutedsl::proof::offset_lemmas::lemma_offset_upper_bound(c.layout, lin);
    //  c.layout.offset(lin) < cosize_nonneg() <= data_size
    //  And gemm_c_tile_offset == idx as int == c.layout.offset(lin)
}

///  All GEMM CTA writes land within the C buffer.
proof fn lemma_gemm_writes_in_bounds(
    config: &GemmDispatchConfig,
    c: &GemmBufferBinding,
)
    requires
        config.bm > 0,
        config.bn > 0,
        config.grid_x > 0,
        c.layout.valid(),
        c.layout.rank() == 2,
        c.layout.non_negative_strides(),
        config.m <= c.layout.shape[0],
        config.n <= c.layout.shape[1],
        tensor_valid(&TensorSpec { layout: c.layout, data_size: c.data_size }),
        grid_matches_tiles(config),
    ensures
        forall|w: nat, idx: nat|
            w < config.grid_x * config.grid_y
            && #[trigger] gemm_wg_write_set(config, &c.layout, w).contains(idx)
            ==> idx < c.data_size,
{
    //  Prove: for any (ti, tj, ei, ej, idx) satisfying is_valid_cta_write, idx < data_size
    assert forall|ti: nat, tj: nat, ei: nat, ej: nat, idx: nat|
        #[trigger] is_valid_cta_write(config, &c.layout, ti, tj, ei, ej, idx)
        implies idx < c.data_size
    by {
        lemma_valid_cta_write_in_bounds(config, c, ti, tj, ei, ej, idx);
    }
    //  Z3 combines this universal with the existential from write_set membership
}

//  ── Master Theorem ───────────────────────────────────────────────────

///  Master theorem: parallel GEMM dispatch equals sequential execution.
///  When `gemm_dispatch_safe` holds, parallel GPU dispatch (all workgroups
///  fire simultaneously) produces the same result as sequential execution
///  (workgroups applied one at a time in order).
pub proof fn lemma_gemm_parallel_dispatch_correct(
    config: &GemmDispatchConfig,
    a: &GemmBufferBinding,
    b: &GemmBufferBinding,
    c: &GemmBufferBinding,
    limits: ComputeLimits,
    a_data: Seq<i64>,
    b_data: Seq<i64>,
    initial_c_data: Seq<int>,
)
    requires
        gemm_dispatch_safe(config, a, b, c, limits),
        initial_c_data.len() == c.data_size,
    ensures ({
        let k = gemm_as_parallel_kernel(config, c, &a.layout, &b.layout, a_data, b_data);
        parallel_result(k, initial_c_data)
            =~= sequential_result(k, initial_c_data, k.num_workgroups)
    }),
{
    let k = gemm_as_parallel_kernel(config, c, &a.layout, &b.layout, a_data, b_data);

    //  Extract key facts from gemm_dispatch_safe for sub-lemma preconditions
    //  grid_x > 0: num_tiles_ceil(m, bm) >= 1 when m > 0 && bm > 0
    //  grid_x > 0: ceil_div(m, bm) = (m + bm - 1) / bm >= bm / bm = 1
    let den = config.bm as int;
    let num = (config.m + config.bm - 1) as int;
    assert(num >= den);  //  m >= 1 implies m + bm - 1 >= bm
    vstd::arithmetic::div_mod::lemma_div_by_self(den);
    vstd::arithmetic::div_mod::lemma_div_is_ordered(den, num, den);
    assert(config.grid_x > 0);

    //  1. CuTe correctness properties
    lemma_gemm_dispatch_safe_implies_correct(config, a, b, c, limits);

    //  2. Write disjointness: distinct workgroups write disjoint C indices
    lemma_gemm_disjoint_bridge(config, &c.layout);

    //  3. Write in-bounds: all writes land within C buffer
    lemma_gemm_writes_in_bounds(config, c);

    //  4. Apply the general parallel ↔ sequential equivalence theorem
    lemma_parallel_equals_sequential(k, initial_c_data);
}

} //  verus!
