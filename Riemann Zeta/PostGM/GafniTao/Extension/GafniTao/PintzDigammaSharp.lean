import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries

/-!
# A sharp real-part bound for the digamma function

The usual strip bound for `‖digamma z‖` loses an unspecified multiple of
`log |Im z|`.  Pintz's single-zeta approximate functional equation needs the
coefficient of that logarithm to be one.  This file obtains it directly from
the absolutely convergent digamma series: the first `ceil |Im z| + 1` real
parts are bounded by the harmonic sum, while the remaining norm-tail is
uniformly bounded.
-/

open Complex Filter Finset Nat

namespace GafniTao

noncomputable section

set_option maxHeartbeats 800000

/-- On a compact substrip of the right half-plane, the real part of digamma
is at most `log (|Im z| + 2)` plus a uniform constant.  The coefficient one
is the sharp feature used by the horizontal Gamma-ratio estimate. -/
theorem exists_re_digamma_le_log_add {a b : ℝ} (ha : 0 < a) :
    ∃ D : ℝ, 0 < D ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      (Complex.digamma z).re ≤ Real.log (|z.im| + 2) + D := by
  let c : ℝ := min a 1
  have hc : 0 < c := lt_min ha one_pos
  have hc1 : c ≤ 1 := min_le_right _ _
  let D : ℝ := 2 + |Real.eulerMascheroniConstant| + (|b| + 2) / c
  have hD : 0 < D := by
    dsimp only [D]
    positivity
  refine ⟨D, hD, ?_⟩
  intro z hza hzb
  have hre : 0 < z.re := lt_of_lt_of_le ha hza
  have hzc : c ≤ z.re := le_trans (min_le_left _ _) hza
  have hb0 : 0 < b := lt_of_lt_of_le hre hzb
  have hpoles : ∀ n : ℕ, z ≠ -(n : ℂ) := by
    intro n hz
    have hzre := congrArg Complex.re hz
    simp only [neg_re, natCast_re] at hzre
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  let f : ℕ → ℂ := fun n =>
    ((n : ℂ) + 1)⁻¹ - (z + n)⁻¹
  have hsum : HasSum f (Complex.digamma z + Real.eulerMascheroniConstant) := by
    have h := Complex.hasSum_digamma hpoles
    have heq :
        (fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + z)) = f := by
      funext n
      simp only [f, one_div]
      rw [add_comm (n : ℂ) z]
    rwa [heq] at h
  let N : ℕ := ⌈|z.im|⌉₊ + 1
  have him0 : (0 : ℝ) ≤ |z.im| := abs_nonneg _
  have hN1 : 1 ≤ N := by dsimp only [N]; omega
  have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := by linarith
  have hNle : (N : ℝ) ≤ |z.im| + 2 := by
    dsimp only [N]
    push_cast
    have hceil := Nat.ceil_lt_add_one him0
    linarith
  have himleN : |z.im| ≤ (N : ℝ) := by
    dsimp only [N]
    push_cast
    exact le_trans (Nat.le_ceil _) (by linarith)
  let L : ℝ := Real.log (|z.im| + 2)
  have hlogN : Real.log (N : ℝ) ≤ L := by
    dsimp only [L]
    exact Real.log_le_log hNpos hNle
  have hmaj : Summable (fun m : ℕ =>
      (‖z‖ + 1) / (c * ((m : ℝ) + 1) ^ 2)) := by
    refine (Complex.summable_one_div_natCast_add_one_sq.mul_left
      ((‖z‖ + 1) / c)).congr fun m => ?_
    rw [mul_one_div, div_div]
  have hnormsum : Summable (fun n : ℕ => ‖f n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => Complex.norm_inv_add_one_sub_inv_le hc hc1 hzc
        (le_refl ‖z‖) n) hmaj
  have hhead :
      (∑ n ∈ Finset.range N, (f n).re) ≤ 1 + L := by
    calc
      (∑ n ∈ Finset.range N, (f n).re) ≤
          ∑ n ∈ Finset.range N, ((n : ℝ) + 1)⁻¹ := by
        apply Finset.sum_le_sum
        intro n _hn
        have hdenRe : 0 < (z + n).re := by
          simp only [add_re, natCast_re]
          positivity
        have hinvRe : 0 ≤ ((z + n)⁻¹).re := by
          rw [Complex.inv_re]
          exact div_nonneg hdenRe.le (Complex.normSq_nonneg _)
        change (((n : ℂ) + 1)⁻¹).re - ((z + n)⁻¹).re ≤
          ((n : ℝ) + 1)⁻¹
        have hone : (((n : ℂ) + 1)⁻¹).re = ((n : ℝ) + 1)⁻¹ := by
          have hc : (n : ℂ) + 1 = ((n : ℝ) + 1 : ℝ) := by norm_num
          rw [hc, Complex.inv_re, Complex.normSq_ofReal, Complex.ofReal_re]
          field_simp
        rw [hone]
        exact sub_le_self _ hinvRe
      _ = ((harmonic N : ℚ) : ℝ) :=
        Complex.sum_inv_natCast_add_one_real N
      _ ≤ 1 + Real.log (N : ℝ) := harmonic_le_one_add_log N
      _ ≤ 1 + L := by linarith
  have hshiftNorm : Summable (fun i : ℕ => ‖f (i + N)‖) :=
    (summable_nat_add_iff N).mpr hnormsum
  have hshiftMaj : Summable (fun i : ℕ =>
      (‖z‖ + 1) / (c * (((i + N : ℕ) : ℝ) + 1) ^ 2)) :=
    (summable_nat_add_iff N).mpr hmaj
  have htailNorm : ‖∑' i : ℕ, f (i + N)‖ ≤ (b + 2) / c := by
    have hzNorm : ‖z‖ ≤ b + |z.im| := by
      have h₁ : ‖z‖ ≤ |z.re| + |z.im| := norm_le_abs_re_add_abs_im z
      have h₂ : |z.re| = z.re := abs_of_pos hre
      linarith
    have hNKey : ‖z‖ + 1 ≤ (b + 2) * (N : ℝ) := by
      have h₁ : b * 1 ≤ b * (N : ℝ) :=
        mul_le_mul_of_nonneg_left hN1R hb0.le
      have h₂ : (b + 2) * (N : ℝ) = b * N + 2 * N := by ring
      rw [h₂]
      linarith
    calc
      ‖∑' i : ℕ, f (i + N)‖ ≤ ∑' i : ℕ, ‖f (i + N)‖ :=
        norm_tsum_le_tsum_norm hshiftNorm
      _ ≤ ∑' i : ℕ,
          (‖z‖ + 1) / (c * (((i + N : ℕ) : ℝ) + 1) ^ 2) :=
        hshiftNorm.tsum_le_tsum
          (fun i => Complex.norm_inv_add_one_sub_inv_le hc hc1 hzc
            (le_refl ‖z‖) (i + N)) hshiftMaj
      _ = (‖z‖ + 1) / c *
          ∑' i : ℕ, 1 / (((i + N : ℕ) : ℝ) + 1) ^ 2 := by
        rw [← tsum_mul_left]
        exact tsum_congr fun i => by rw [mul_one_div, div_div]
      _ ≤ (‖z‖ + 1) / c * (N : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_left
          (Complex.tsum_one_div_natCast_add_add_one_sq_le hN1)
          (by positivity)
      _ = ((‖z‖ + 1) * (N : ℝ)⁻¹) / c := by ring
      _ ≤ (b + 2) / c := by
        have h₂ : (‖z‖ + 1) * (N : ℝ)⁻¹ ≤ b + 2 := by
          rw [← div_eq_mul_inv, div_le_iff₀ hNpos]
          linarith
        gcongr
  have hsplit :
      (∑ n ∈ Finset.range N, f n) + ∑' i : ℕ, f (i + N) = ∑' n : ℕ, f n :=
    hsum.summable.sum_add_tsum_nat_add N
  have htailRe : (∑' i : ℕ, f (i + N)).re ≤ (b + 2) / c :=
    (Complex.re_le_norm _).trans htailNorm
  have hseriesRe : (∑' n : ℕ, f n).re ≤ 1 + L + (b + 2) / c := by
    rw [← hsplit, add_re]
    simpa only [Complex.re_sum] using add_le_add hhead htailRe
  have hdigamma : Complex.digamma z =
      (∑' n : ℕ, f n) - (Real.eulerMascheroniConstant : ℂ) := by
    rw [hsum.tsum_eq]
    ring
  rw [hdigamma, sub_re, Complex.ofReal_re]
  have hgamma :
      -Real.eulerMascheroniConstant ≤ |Real.eulerMascheroniConstant| :=
    neg_le_abs _
  have hbAbs : (b + 2) / c ≤ (|b| + 2) / c := by
    gcongr
    exact le_abs_self b
  dsimp only [D]
  linarith

#print axioms exists_re_digamma_le_log_add

set_option maxHeartbeats 200000

end

end GafniTao
