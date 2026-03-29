use vstd::prelude::*;
use crate::gemm_dispatch::*;
use crate::compute_validation::*;
use verus_cutedsl::layout::*;
use verus_cutedsl::shape::*;
use verus_cutedsl::gemm::*;
use verus_cutedsl::predication::*;

verus! {

//  ── SM80 Configuration Constants ────────────────────────────────────────

pub open spec fn sm80_bm() -> nat { 128 }
pub open spec fn sm80_bn() -> nat { 128 }
pub open spec fn sm80_bk() -> nat { 32 }

//  ── Layout Helpers ──────────────────────────────────────────────────────

pub open spec fn row_major_2d(rows: nat, cols: nat) -> LayoutSpec {
    make_row_major(seq![rows, cols])
}

pub open spec fn sm80_gemm_config(m: nat, n: nat, k: nat) -> GemmDispatchConfig {
    GemmDispatchConfig {
        m, n, k,
        bm: sm80_bm(),
        bn: sm80_bn(),
        bk: sm80_bk(),
        grid_x: num_tiles_ceil(m, sm80_bm()),
        grid_y: num_tiles_ceil(n, sm80_bn()),
    }
}

pub open spec fn sm80_a_binding(m: nat, k: nat) -> GemmBufferBinding {
    GemmBufferBinding { layout: row_major_2d(m, k), data_size: m * k }
}

pub open spec fn sm80_b_binding(k: nat, n: nat) -> GemmBufferBinding {
    GemmBufferBinding { layout: row_major_2d(k, n), data_size: k * n }
}

pub open spec fn sm80_c_binding(m: nat, n: nat) -> GemmBufferBinding {
    GemmBufferBinding { layout: row_major_2d(m, n), data_size: m * n }
}

//  ── Row-major stride values for rank 2 ──────────────────────────────────

///  For shape [rows, cols], row_major strides = [cols, 1].
proof fn lemma_row_major_2d_stride_values(rows: nat, cols: nat)
    requires rows > 0, cols > 0,
    ensures
        row_major_strides(seq![rows, cols]) =~= seq![cols as int, 1int],
{
    let shape = seq![rows, cols];
    let rev_shape = seq_reverse(shape);
    assert(rev_shape =~= seq![cols, rows]);

    //  column_major_strides([cols, rows])
    //  = [1] ++ scale_strides(column_major_strides([rows]), cols)
    //  column_major_strides([rows]) = [1] ++ scale_strides(column_major_strides([]), rows)
    //                               = [1] ++ scale_strides([], rows) = [1]
    assert(seq![rows as nat].skip(1) =~= Seq::<nat>::empty());
    assert(column_major_strides(Seq::<nat>::empty()) =~= Seq::<int>::empty());
    assert(column_major_strides(seq![rows as nat]) =~= seq![1int]) by {
        assert(scale_strides_spec(Seq::<int>::empty(), rows as int) =~= Seq::<int>::empty());
    }

    //  column_major_strides([cols, rows]) = [1, cols]
    assert(rev_shape.skip(1) =~= seq![rows as nat]);
    let cm = column_major_strides(rev_shape);
    let scaled = scale_strides_spec(seq![1int], cols as int);
    assert(scaled.len() == 1);
    assert(scaled[0] == 1int * (cols as int));
    assert(scaled =~= seq![cols as int]);
    assert(cm =~= seq![1int, cols as int]);

    //  row_major_strides = reverse(cm) = [cols, 1]
    assert(seq_reverse(cm) =~= seq![cols as int, 1int]);
}

//  ── Row-major layout properties ─────────────────────────────────────────

pub proof fn lemma_row_major_2d_valid(rows: nat, cols: nat)
    requires rows > 0, cols > 0,
    ensures
        row_major_2d(rows, cols).valid(),
        row_major_2d(rows, cols).rank() == 2,
        row_major_2d(rows, cols).shape[0] == rows,
        row_major_2d(rows, cols).shape[1] == cols,
{
    assert(shape_valid(seq![rows, cols]));
    verus_cutedsl::proof::injectivity_lemmas::lemma_row_major_valid(seq![rows, cols]);
    //  valid implies stride.len() == shape.len() == 2
    lemma_row_major_2d_stride_values(rows, cols);
}

pub proof fn lemma_row_major_2d_injective(rows: nat, cols: nat)
    requires rows > 0, cols > 0,
    ensures row_major_2d(rows, cols).is_injective(),
{
    assert(shape_valid(seq![rows, cols]));
    verus_cutedsl::proof::injectivity_lemmas::lemma_row_major_injective(seq![rows, cols]);
}

pub proof fn lemma_row_major_2d_nonneg_strides(rows: nat, cols: nat)
    requires rows > 0, cols > 0,
    ensures row_major_2d(rows, cols).non_negative_strides(),
{
    lemma_row_major_2d_valid(rows, cols);
    lemma_row_major_2d_stride_values(rows, cols);
    let layout = row_major_2d(rows, cols);
    assert(layout.stride =~= seq![cols as int, 1int]);
    assert forall|i: int| 0 <= i < layout.stride.len()
        implies #[trigger] layout.stride[i] >= 0
    by {
        if i == 0 { assert(layout.stride[0] == cols as int); }
        else { assert(layout.stride[1] == 1int); }
    }
}

pub proof fn lemma_row_major_2d_tensor_valid(rows: nat, cols: nat)
    requires rows > 0, cols > 0,
    ensures
        tensor_valid(&TensorSpec {
            layout: row_major_2d(rows, cols),
            data_size: rows * cols,
        }),
{
    let layout = row_major_2d(rows, cols);
    lemma_row_major_2d_valid(rows, cols);
    lemma_row_major_2d_nonneg_strides(rows, cols);
    lemma_row_major_2d_stride_values(rows, cols);

    //  Directly unfold cosize_nonneg for rank 2 (needs 3 levels: rank 2 → 1 → 0)
    assert(layout.stride =~= seq![cols as int, 1int]);
    reveal_with_fuel(LayoutSpec::cosize_nonneg, 3);

    //  Unfold cosize_nonneg step by step for rank 2
    assert(layout.shape.len() > 0);
    let rest = LayoutSpec { shape: layout.shape.skip(1), stride: layout.stride.skip(1) };
    assert(rest.shape =~= seq![cols]);
    assert(rest.stride =~= seq![1int]);
    assert(rest.shape.len() > 0);

    let rest2 = LayoutSpec { shape: rest.shape.skip(1), stride: rest.stride.skip(1) };
    assert(rest2.shape.len() == 0);

    //  Level 2 (base): empty shape → cosize = 1
    assert(rest2.cosize_nonneg() == 1nat);

    //  Level 1: shape [cols], stride [1] → cosize = (cols-1)*1 + 1 = cols
    assert(rest.shape.first() == cols);
    assert(rest.stride.first() == 1int);
    assert(rest.cosize_nonneg() == ((cols - 1) * 1 + 1) as nat);

    //  Level 0: shape [rows, cols], stride [cols, 1] → cosize = (rows-1)*cols + cols
    assert(layout.shape.first() == rows);
    assert(layout.stride.first() == cols as int);
    assert(layout.cosize_nonneg() == ((rows - 1) * cols + rest.cosize_nonneg()) as nat);

    assert(layout.cosize_nonneg() as int <= (rows * cols) as int) by (nonlinear_arith)
        requires
            rows > 0, cols > 0,
            layout.cosize_nonneg() == ((rows - 1) * cols + cols) as nat;
}

//  ── SM80 Master Safety Lemma ────────────────────────────────────────────

///  SM80 GEMM is safe for any matrix dimensions within dispatch limits.
pub proof fn lemma_sm80_gemm_safe(
    m: nat, n: nat, k: nat,
    limits: ComputeLimits,
)
    requires
        m > 0, n > 0, k > 0,
        num_tiles_ceil(m, sm80_bm()) <= limits.max_group_count_x,
        num_tiles_ceil(n, sm80_bn()) <= limits.max_group_count_y,
        1 <= limits.max_group_count_z,
    ensures
        gemm_dispatch_safe(
            &sm80_gemm_config(m, n, k),
            &sm80_a_binding(m, k),
            &sm80_b_binding(k, n),
            &sm80_c_binding(m, n),
            limits,
        ),
{
    //  Prove row-major properties for all three matrices
    lemma_row_major_2d_valid(m, k);
    lemma_row_major_2d_valid(k, n);
    lemma_row_major_2d_valid(m, n);
    lemma_row_major_2d_injective(m, n);
    lemma_row_major_2d_nonneg_strides(m, n);
    lemma_row_major_2d_tensor_valid(m, k);
    lemma_row_major_2d_tensor_valid(k, n);
    lemma_row_major_2d_tensor_valid(m, n);
}

} //  verus!
