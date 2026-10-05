import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Coefficient-one real digamma bounds

The actual convergent digamma series is split at the norm scale. The
harmonic head is kept with coefficient one; the remaining head and tail
have absolute bounds on the half-plane needed by the source.
-/

namespace DongWangWangZhang2026
noncomputable section
open Complex Finset

/-- Moving a complex number to the right cannot decrease its norm in the right half-plane. -/
theorem norm_le_norm_add_nat {z : ℂ} (hz : 0 ≤ z.re) (n : ℕ) :
    ‖z‖ ≤ ‖z + (n : ℂ)‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [Complex.sq_norm, normSq_apply, add_re, add_im, natCast_re, natCast_im,
    add_zero]
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

/-- The nonharmonic real head of the digamma series is uniformly bounded at the norm scale. -/
theorem digamma_real_head_le {z : ℂ} (hz : 1 / 4 ≤ z.re)
    {N : ℕ} (hN : (N : ℝ) ≤ ‖z‖ + 2) :
    0 ≤ (∑ n ∈ range N, ((z + (n : ℂ))⁻¹).re) ∧
      (∑ n ∈ range N, ((z + (n : ℂ))⁻¹).re) ≤ 9 := by
  have hzpos : 0 < z.re := by linarith
  have hR : 0 < ‖z‖ := lt_of_lt_of_le hzpos (re_le_norm z)
  constructor
  · apply sum_nonneg
    intro n _
    rw [inv_re, add_re, natCast_re]
    exact div_nonneg (by positivity) (normSq_nonneg _)
  · calc
      (∑ n ∈ range N, ((z + (n : ℂ))⁻¹).re) ≤ ∑ _n ∈ range N, ‖z‖⁻¹ := by
        apply sum_le_sum
        intro n _
        calc
          ((z + (n : ℂ))⁻¹).re ≤ ‖(z + (n : ℂ))⁻¹‖ := re_le_norm _
          _ = ‖z + (n : ℂ)‖⁻¹ := norm_inv _
          _ ≤ ‖z‖⁻¹ := inv_anti₀ hR (norm_le_norm_add_nat hzpos.le n)
      _ = (N : ℝ) / ‖z‖ := by simp [div_eq_mul_inv]
      _ ≤ 9 := by
        rw [div_le_iff₀ hR]
        linarith [re_le_norm z]

/-- The complex tail after the norm scale has an absolute bound. -/
theorem digamma_norm_tail_le {z : ℂ} (hz : 1 / 4 ≤ z.re)
    {N : ℕ} (hN : 1 ≤ N) (hR : ‖z‖ + 1 ≤ (N : ℝ)) :
    ‖∑' i : ℕ, ((((i + N : ℕ) : ℂ) + 1)⁻¹ - (z + (i + N : ℕ))⁻¹)‖ ≤ 4 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hmaj : Summable (fun n : ℕ => (‖z‖ + 1) / ((1 / 4) * ((n : ℝ) + 1) ^ 2)) := by
    refine (summable_one_div_natCast_add_one_sq.mul_left ((‖z‖ + 1) / (1 / 4))).congr
      fun n => ?_
    rw [mul_one_div, div_div]
  have hnorm : Summable (fun n : ℕ => ‖((n : ℂ) + 1)⁻¹ - (z + n)⁻¹‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => norm_inv_add_one_sub_inv_le (by norm_num : (0 : ℝ) < 1 / 4)
        (by norm_num) hz le_rfl n) hmaj
  have hshift := (summable_nat_add_iff N).mpr hnorm
  have hshiftmaj := (summable_nat_add_iff N).mpr hmaj
  calc
    ‖∑' i : ℕ, ((((i + N : ℕ) : ℂ) + 1)⁻¹ - (z + (i + N : ℕ))⁻¹)‖
        ≤ ∑' i : ℕ, ‖(((i + N : ℕ) : ℂ) + 1)⁻¹ - (z + (i + N : ℕ))⁻¹‖ :=
      norm_tsum_le_tsum_norm hshift
    _ ≤ ∑' i : ℕ, (‖z‖ + 1) / ((1 / 4) * (((i + N : ℕ) : ℝ) + 1) ^ 2) :=
      hshift.tsum_le_tsum (fun i =>
        norm_inv_add_one_sub_inv_le (by norm_num : (0 : ℝ) < 1 / 4)
          (by norm_num) hz le_rfl (i + N)) hshiftmaj
    _ = ((‖z‖ + 1) / (1 / 4)) *
        ∑' i : ℕ, 1 / (((i + N : ℕ) : ℝ) + 1) ^ 2 := by
      rw [← tsum_mul_left]
      exact tsum_congr fun i => by rw [mul_one_div, div_div]
    _ ≤ ((‖z‖ + 1) / (1 / 4)) * (N : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left (tsum_one_div_natCast_add_add_one_sq_le hN) (by positivity)
    _ ≤ 4 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hNpos]
      linarith

/-- Coefficient one in the real digamma logarithm, uniformly on an unbounded half-plane. -/
theorem abs_re_digamma_sub_log_norm_le {z : ℂ} (hz : 1 / 4 ≤ z.re) :
    |(digamma z).re - Real.log (‖z‖ + 2)| ≤
      14 + |Real.eulerMascheroniConstant| := by
  let N : ℕ := ⌈‖z‖⌉₊ + 1
  have hN1 : 1 ≤ N := Nat.le_add_left 1 _
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN1)
  have hNlower : ‖z‖ + 1 ≤ (N : ℝ) := by
    dsimp only [N]
    push_cast
    linarith [Nat.le_ceil ‖z‖]
  have hNupper : (N : ℝ) ≤ ‖z‖ + 2 := by
    dsimp only [N]
    push_cast
    linarith [Nat.ceil_lt_add_one (norm_nonneg z)]
  have hhead := digamma_real_head_le hz hNupper
  have htail := digamma_norm_tail_le hz hN1 hNlower
  have hsum := hasSum_digamma_of_re_pos (z₀ := z) (by linarith)
  have hsplit := hsum.summable.sum_add_tsum_nat_add N
  rw [hsum.tsum_eq] at hsplit
  have hre := congrArg Complex.re hsplit
  simp only [sum_sub_distrib, sum_inv_natCast_add_one, sub_re, add_re,
    ratCast_re, ofReal_re] at hre
  rw [re_sum] at hre
  have hHlow : Real.log (‖z‖ + 2) ≤ (harmonic N : ℝ) := by
    apply le_trans ?_ (log_add_one_le_harmonic N)
    apply Real.log_le_log (by positivity)
    push_cast
    linarith
  have hHup : (harmonic N : ℝ) ≤ 1 + Real.log (‖z‖ + 2) := by
    apply (harmonic_le_one_add_log N).trans
    linarith [Real.log_le_log hNpos hNupper]
  have htup := (re_le_norm
    (∑' i : ℕ, ((((i + N : ℕ) : ℂ) + 1)⁻¹ - (z + (i + N : ℕ))⁻¹))).trans htail
  have htlow := (abs_le.mp (abs_re_le_norm
    (∑' i : ℕ, ((((i + N : ℕ) : ℂ) + 1)⁻¹ - (z + (i + N : ℕ))⁻¹)))).1
  apply abs_le.mpr
  constructor <;> linarith [le_abs_self Real.eulerMascheroniConstant,
    neg_abs_le Real.eulerMascheroniConstant]

/-- The source half-argument gamma bound retains coefficient one for arbitrarily large real part. -/
theorem re_digamma_source_upper {a v : ℝ} (ha : 0 < a) (hv : 2 ≤ |v|) :
    (digamma ((((1 + a : ℝ) : ℂ) + (v : ℂ) * I) / 2)).re ≤
      Real.log (2 + a + |v|) + (14 + |Real.eulerMascheroniConstant|) := by
  let z : ℂ := (((1 + a : ℝ) : ℂ) + (v : ℂ) * I) / 2
  have hre : z.re = (1 + a) / 2 := by simp [z]
  have him : z.im = v / 2 := by simp [z]
  have hq : 1 / 4 ≤ z.re := by rw [hre]; linarith
  have h := (abs_le.mp (abs_re_digamma_sub_log_norm_le hq)).2
  have hn : ‖z‖ + 2 ≤ 2 + a + |v| := by
    have hb := norm_le_abs_re_add_abs_im z
    rw [hre, him, abs_of_pos (by linarith : 0 < (1 + a) / 2),
      abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hb
    linarith
  have hl := Real.log_le_log (by positivity : 0 < ‖z‖ + 2) hn
  linarith

end
end DongWangWangZhang2026
