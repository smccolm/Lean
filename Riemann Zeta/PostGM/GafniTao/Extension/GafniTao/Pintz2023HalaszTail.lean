import GafniTao.Pintz2023HalaszDyadic

/-!
# Quantitative tail of Pintz's smoothed Gram series

The source truncates beyond `N log^2 N`.  Here the complete infinite tail is
kept and bounded by an explicit geometric series, including the first omitted
integer.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- In the half-plane `Re s >= 0`, one smoothed term is bounded by the first
exponential in the literal Halasz kernel. -/
theorem norm_pintz2023SmoothedZetaTerm_le_exp
    {N n : ℕ} {s : ℂ} (hN : 0 < N) (hn : 0 < n) (hs : 0 ≤ s.re) :
    ‖pintz2023SmoothedZetaTerm N s n‖ ≤
      Real.exp (-(n : ℝ) / (2 * N)) := by
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hKernelPos := pintz2023HalaszKernel_pos hN hn
  have hKernelExp : pintz2023HalaszKernel N n ≤
      Real.exp (-(n : ℝ) / (2 * N)) := by
    unfold pintz2023HalaszKernel
    linarith [Real.exp_pos (-(n : ℝ) / N)]
  have hpow : ‖(n : ℂ) ^ (-s)‖ ≤ 1 := by
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos hnReal]
    have hexponent : (-s).re = -s.re := by simp
    rw [hexponent]
    exact Real.rpow_le_one_of_one_le_of_nonpos hnOne (neg_nonpos.mpr hs)
  rw [pintz2023SmoothedZetaTerm_eq hn, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hKernelPos]
  calc
    pintz2023HalaszKernel N n * ‖(n : ℂ) ^ (-s)‖ ≤
        Real.exp (-(n : ℝ) / (2 * N)) * 1 :=
      mul_le_mul hKernelExp hpow (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := mul_one _

/-- Exact geometric majorant for the complete tail after `M`. -/
theorem norm_pintz2023SmoothedZetaSum_sub_sum_Icc_le
    {N M : ℕ} {s : ℂ} (hN : 0 < N) (hs : 0 ≤ s.re) :
    ‖pintz2023SmoothedZetaSum N s -
        ∑ n ∈ Finset.Icc 1 M, pintz2023SmoothedZetaTerm N s n‖ ≤
      Real.exp (-((M + 1 : ℕ) : ℝ) / (2 * N)) *
        (1 - Real.exp (-(1 : ℝ) / (2 * N)))⁻¹ := by
  let f : ℕ → ℂ := fun n => pintz2023SmoothedZetaTerm N s n
  let q : ℝ := Real.exp (-(1 : ℝ) / (2 * N))
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have hqPos : 0 < q := by dsimp only [q]; positivity
  have hqLt : q < 1 := by
    dsimp only [q]
    rw [Real.exp_lt_one_iff]
    exact div_neg_of_neg_of_pos (by norm_num) (by positivity)
  have hqNorm : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hqPos]; exact hqLt
  have hf : Summable f := summable_pintz2023SmoothedZetaTerm hN hs
  have hTailIdentity :
      pintz2023SmoothedZetaSum N s -
          ∑ n ∈ Finset.Icc 1 M, pintz2023SmoothedZetaTerm N s n =
        ∑' i : ℕ, f (i + (M + 1)) := by
    have hSplit := hf.sum_add_tsum_nat_add (M + 1)
    have hFinite : (∑ i ∈ Finset.range (M + 1), f i) =
        ∑ n ∈ Finset.Icc 1 M, pintz2023SmoothedZetaTerm N s n := by
      rw [← sum_Icc_pintz2023SmoothedZetaTerm_eq N M s]
    dsimp only [f] at hSplit ⊢
    rw [hFinite] at hSplit
    unfold pintz2023SmoothedZetaSum
    rw [← hSplit]
    ring
  have hPointwise : ∀ i : ℕ, ‖f (i + (M + 1))‖ ≤
      Real.exp (-((M + 1 : ℕ) : ℝ) / (2 * N)) * q ^ i := by
    intro i
    have hn : 0 < i + (M + 1) := by omega
    have hTerm := norm_pintz2023SmoothedZetaTerm_le_exp hN hn hs
    calc
      ‖f (i + (M + 1))‖ ≤
          Real.exp (-((i + (M + 1) : ℕ) : ℝ) / (2 * N)) := hTerm
      _ = Real.exp (-((M + 1 : ℕ) : ℝ) / (2 * N)) * q ^ i := by
        dsimp only [q]
        rw [← Real.exp_nat_mul]
        rw [← Real.exp_add]
        congr 1
        push_cast
        field_simp
        ring
  have hGeom : Summable (fun i : ℕ =>
      Real.exp (-((M + 1 : ℕ) : ℝ) / (2 * N)) * q ^ i) :=
    (summable_geometric_of_norm_lt_one hqNorm).mul_left _
  have hNormSummable : Summable (fun i : ℕ => ‖f (i + (M + 1))‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hPointwise hGeom
  rw [hTailIdentity]
  calc
    ‖∑' i : ℕ, f (i + (M + 1))‖ ≤
        ∑' i : ℕ, ‖f (i + (M + 1))‖ :=
      norm_tsum_le_tsum_norm hNormSummable
    _ ≤ ∑' i : ℕ,
        Real.exp (-((M + 1 : ℕ) : ℝ) / (2 * N)) * q ^ i :=
      hNormSummable.tsum_le_tsum hPointwise hGeom
    _ = Real.exp (-((M + 1 : ℕ) : ℝ) / (2 * N)) *
        (1 - q)⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hqNorm]
    _ = _ := by rfl

#print axioms norm_pintz2023SmoothedZetaTerm_le_exp
#print axioms norm_pintz2023SmoothedZetaSum_sub_sum_Icc_le

end

end GafniTao
