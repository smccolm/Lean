import GafniTao.FordEulerProduct
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Ford's Lemma 5.1

This file assembles the exact Euler-product, hyperbolic Fourier-transform and
nonnegative trigonometric-polynomial inputs into Ford's Lemma 5.1.  All
infinite sum/integral exchanges are mediated by explicit absolute
summability statements.
-/

namespace GafniTao

/-- The nonnegative prime-power coefficient on the line `re s = 1 + eta`.
The term at `m=0` is zero, so the natural-number index exactly implements
Ford's `m >= 1` convention. -/
noncomputable def fordPrimePowerWeight
    (eta : ℝ) (p : Nat.Primes) (m : ℕ) : ℝ :=
  (p : ℝ) ^ (-(m : ℝ) * (1 + eta)) / m

theorem fordPrimePowerWeight_nonneg
    (eta : ℝ) (p : Nat.Primes) (m : ℕ) :
    0 ≤ fordPrimePowerWeight eta p m := by
  exact div_nonneg (Real.rpow_nonneg (by exact_mod_cast p.prop.pos.le) _)
    (Nat.cast_nonneg m)

theorem fordPrimePowerWeight_eq_term_re
    (eta : ℝ) (p : Nat.Primes) (m : ℕ) :
    fordPrimePowerWeight eta p m =
      (((((p : ℂ) ^ (-fordZetaLine eta 0)) ^ m) / m).re) := by
  rw [ford_prime_power_term_re eta 0 p m]
  simp [fordPrimePowerWeight]

theorem summable_fordPrimePowerWeight_fixed_prime
    {eta : ℝ} (heta : 0 < eta) (p : Nat.Primes) :
    Summable (fordPrimePowerWeight eta p) := by
  have hs : 1 < (fordZetaLine eta 0).re := by
    simp only [fordZetaLine_re]
    linarith
  have hComplex := (ford_prime_log_hasSum hs p).summable
  have hReal : Summable
      (fun m : ℕ => (((((p : ℂ) ^ (-fordZetaLine eta 0)) ^ m) / m).re)) := by
    simpa only [Function.comp_apply] using
      (hComplex.hasSum.map Complex.reCLM Complex.continuous_re).summable
  exact hReal.congr fun m => (fordPrimePowerWeight_eq_term_re eta p m).symm

theorem tsum_fordPrimePowerWeight_fixed_prime
    {eta : ℝ} (heta : 0 < eta) (p : Nat.Primes) :
    (∑' m : ℕ, fordPrimePowerWeight eta p m) =
      (-Complex.log
        (1 - (p : ℂ) ^ (-fordZetaLine eta 0))).re := by
  have hs : 1 < (fordZetaLine eta 0).re := by
    simp only [fordZetaLine_re]
    linarith
  rw [re_ford_prime_log_eq_tsum hs p]
  apply tsum_congr
  intro m
  exact fordPrimePowerWeight_eq_term_re eta p m

theorem summable_tsum_fordPrimePowerWeight
    {eta : ℝ} (heta : 0 < eta) :
    Summable (fun p : Nat.Primes =>
      ∑' m : ℕ, fordPrimePowerWeight eta p m) := by
  have hs : 1 < (fordZetaLine eta 0).re := by
    simp only [fordZetaLine_re]
    linarith
  have hComplex := summable_fordEulerZetaLog hs
  have hReal : Summable (fun p : Nat.Primes =>
      (-Complex.log
        (1 - (p : ℂ) ^ (-fordZetaLine eta 0))).re) := by
    simpa only [Function.comp_apply] using
      (hComplex.hasSum.map Complex.reCLM Complex.continuous_re).summable
  exact hReal.congr fun p => (tsum_fordPrimePowerWeight_fixed_prime heta p).symm

theorem summable_fordPrimePowerWeight
    {eta : ℝ} (heta : 0 < eta) :
    Summable (fun z : Nat.Primes × ℕ =>
      fordPrimePowerWeight eta z.1 z.2) := by
  rw [summable_prod_of_nonneg
    (fun z => fordPrimePowerWeight_nonneg eta z.1 z.2)]
  exact ⟨summable_fordPrimePowerWeight_fixed_prime heta,
    summable_tsum_fordPrimePowerWeight heta⟩

theorem tsum_fordPrimePowerWeight
    {eta : ℝ} (heta : 0 < eta) :
    (∑' p : Nat.Primes, ∑' m : ℕ, fordPrimePowerWeight eta p m) =
      Real.log ‖riemannZeta (fordZetaLine eta 0)‖ := by
  symm
  rw [log_norm_riemannZeta_fordLine_eq_prime_power_series heta 0]
  apply tsum_congr
  intro p
  apply tsum_congr
  intro m
  simp [fordPrimePowerWeight]

/-- One absolutely integrable prime-power Fourier summand. -/
noncomputable def fordEulerFourierTerm
    (eta t₁ t₂ : ℝ) (z : Nat.Primes × ℕ) (u : ℝ) : ℝ :=
  fordPrimePowerWeight eta z.1 z.2 *
    (Real.cos
      ((z.2 : ℝ) * t₁ * Real.log z.1 +
        ((z.2 : ℝ) * t₂ * Real.log z.1) * u) /
      Real.cosh u ^ 2)

theorem integrable_fordEulerFourierTerm
    (eta t₁ t₂ : ℝ) (z : Nat.Primes × ℕ) :
    MeasureTheory.Integrable (fordEulerFourierTerm eta t₁ t₂ z) := by
  simpa only [fordEulerFourierTerm] using
    (integrable_ford_cos_add_mul_div_cosh_sq
      ((z.2 : ℝ) * t₁ * Real.log z.1)
      ((z.2 : ℝ) * t₂ * Real.log z.1)).const_mul
        (fordPrimePowerWeight eta z.1 z.2)

theorem integral_fordEulerFourierTerm
    (eta t₁ t₂ : ℝ) (z : Nat.Primes × ℕ) :
    (∫ u : ℝ, fordEulerFourierTerm eta t₁ t₂ z u) =
      fordPrimePowerWeight eta z.1 z.2 *
        fordFourierKernel ((z.2 : ℝ) * t₂ * Real.log z.1) *
        Real.cos ((z.2 : ℝ) * t₁ * Real.log z.1) := by
  change (∫ u : ℝ, fordPrimePowerWeight eta z.1 z.2 *
      (Real.cos ((z.2 : ℝ) * t₁ * Real.log z.1 +
        ((z.2 : ℝ) * t₂ * Real.log z.1) * u) / Real.cosh u ^ 2)) = _
  rw [MeasureTheory.integral_const_mul,
    ford_integral_cos_add_mul_div_cosh_sq]
  ring

theorem norm_fordEulerFourierTerm_le
    (eta t₁ t₂ : ℝ) (z : Nat.Primes × ℕ) (u : ℝ) :
    ‖fordEulerFourierTerm eta t₁ t₂ z u‖ ≤
      fordPrimePowerWeight eta z.1 z.2 * (1 / Real.cosh u ^ 2) := by
  have hq := fordPrimePowerWeight_nonneg eta z.1 z.2
  have hcosh : 0 < Real.cosh u ^ 2 := sq_pos_of_pos (Real.cosh_pos u)
  rw [fordEulerFourierTerm, Real.norm_eq_abs, abs_mul, abs_div,
    abs_of_nonneg hq, abs_of_pos hcosh]
  calc
    fordPrimePowerWeight eta z.1 z.2 *
        (|Real.cos ((z.2 : ℝ) * t₁ * Real.log z.1 +
          (z.2 : ℝ) * t₂ * Real.log z.1 * u)| / Real.cosh u ^ 2) =
        (fordPrimePowerWeight eta z.1 z.2 *
          |Real.cos ((z.2 : ℝ) * t₁ * Real.log z.1 +
            (z.2 : ℝ) * t₂ * Real.log z.1 * u)|) / Real.cosh u ^ 2 := by ring
    _ ≤ (fordPrimePowerWeight eta z.1 z.2 * 1) / Real.cosh u ^ 2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) hq) hcosh.le
    _ = fordPrimePowerWeight eta z.1 z.2 * (1 / Real.cosh u ^ 2) := by ring

theorem integral_norm_fordEulerFourierTerm_le
    (eta t₁ t₂ : ℝ) (z : Nat.Primes × ℕ) :
    (∫ u : ℝ, ‖fordEulerFourierTerm eta t₁ t₂ z u‖) ≤
      2 * fordPrimePowerWeight eta z.1 z.2 := by
  have hMajor : MeasureTheory.Integrable
      (fun u : ℝ =>
        fordPrimePowerWeight eta z.1 z.2 * (1 / Real.cosh u ^ 2)) :=
    integrable_one_div_cosh_sq.const_mul _
  calc
    (∫ u : ℝ, ‖fordEulerFourierTerm eta t₁ t₂ z u‖) ≤
        ∫ u : ℝ,
          fordPrimePowerWeight eta z.1 z.2 * (1 / Real.cosh u ^ 2) := by
      exact MeasureTheory.integral_mono
        (integrable_fordEulerFourierTerm eta t₁ t₂ z).norm hMajor
        (norm_fordEulerFourierTerm_le eta t₁ t₂ z)
    _ = fordPrimePowerWeight eta z.1 z.2 * 2 := by
      rw [MeasureTheory.integral_const_mul, integral_one_div_cosh_sq]
    _ = 2 * fordPrimePowerWeight eta z.1 z.2 := by ring

theorem summable_integral_norm_fordEulerFourierTerm
    {eta : ℝ} (heta : 0 < eta) (t₁ t₂ : ℝ) :
    Summable (fun z : Nat.Primes × ℕ =>
      ∫ u : ℝ, ‖fordEulerFourierTerm eta t₁ t₂ z u‖) := by
  exact ((summable_fordPrimePowerWeight heta).mul_left 2).of_nonneg_of_le
    (fun z => MeasureTheory.integral_nonneg fun _ => norm_nonneg _)
    (fun z => integral_norm_fordEulerFourierTerm_le eta t₁ t₂ z)

/-- Fully justified product-indexed Euler/Fourier interchange. -/
theorem integral_tsum_fordEulerFourierTerm
    {eta : ℝ} (heta : 0 < eta) (t₁ t₂ : ℝ) :
    (∫ u : ℝ, ∑' z : Nat.Primes × ℕ,
        fordEulerFourierTerm eta t₁ t₂ z u) =
      ∑' z : Nat.Primes × ℕ,
        fordPrimePowerWeight eta z.1 z.2 *
          fordFourierKernel ((z.2 : ℝ) * t₂ * Real.log z.1) *
          Real.cos ((z.2 : ℝ) * t₁ * Real.log z.1) := by
  rw [← MeasureTheory.integral_tsum_of_summable_integral_norm
    (integrable_fordEulerFourierTerm eta t₁ t₂)
    (summable_integral_norm_fordEulerFourierTerm heta t₁ t₂)]
  apply tsum_congr
  intro z
  exact integral_fordEulerFourierTerm eta t₁ t₂ z

noncomputable def fordEulerRawTerm
    (eta t : ℝ) (z : Nat.Primes × ℕ) : ℝ :=
  fordPrimePowerWeight eta z.1 z.2 *
    Real.cos ((z.2 : ℝ) * t * Real.log z.1)

theorem norm_fordEulerRawTerm_le
    (eta t : ℝ) (z : Nat.Primes × ℕ) :
    ‖fordEulerRawTerm eta t z‖ ≤ fordPrimePowerWeight eta z.1 z.2 := by
  rw [fordEulerRawTerm, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (fordPrimePowerWeight_nonneg eta z.1 z.2)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (Real.abs_cos_le_one ((z.2 : ℝ) * t * Real.log z.1))
    (fordPrimePowerWeight_nonneg eta z.1 z.2)

theorem summable_fordEulerRawTerm
    {eta : ℝ} (heta : 0 < eta) (t : ℝ) :
    Summable (fordEulerRawTerm eta t) :=
  Summable.of_norm <| (summable_fordPrimePowerWeight heta).of_nonneg_of_le
    (fun z => norm_nonneg (fordEulerRawTerm eta t z))
    (norm_fordEulerRawTerm_le eta t)

theorem tsum_fordEulerRawTerm_eq_log_norm
    {eta : ℝ} (heta : 0 < eta) (t : ℝ) :
    (∑' z : Nat.Primes × ℕ, fordEulerRawTerm eta t z) =
      Real.log ‖riemannZeta (fordZetaLine eta t)‖ := by
  have hRaw := summable_fordEulerRawTerm heta t
  rw [hRaw.tsum_prod' (fun p => hRaw.prod_factor p)]
  symm
  rw [log_norm_riemannZeta_fordLine_eq_prime_power_series heta t]
  apply tsum_congr
  intro p
  apply tsum_congr
  intro m
  simp only [fordEulerRawTerm, fordPrimePowerWeight]
  ring

theorem tsum_fordEulerFourierTerm_eq_log_norm_div
    {eta : ℝ} (heta : 0 < eta) (t₁ t₂ u : ℝ) :
    (∑' z : Nat.Primes × ℕ, fordEulerFourierTerm eta t₁ t₂ z u) =
      Real.log ‖riemannZeta (fordZetaLine eta (t₁ + u * t₂))‖ /
        Real.cosh u ^ 2 := by
  calc
    (∑' z : Nat.Primes × ℕ, fordEulerFourierTerm eta t₁ t₂ z u) =
        ∑' z : Nat.Primes × ℕ,
          fordEulerRawTerm eta (t₁ + u * t₂) z *
            (1 / Real.cosh u ^ 2) := by
      apply tsum_congr
      intro z
      simp only [fordEulerFourierTerm, fordEulerRawTerm]
      rw [show (z.2 : ℝ) * t₁ * Real.log z.1 +
          ((z.2 : ℝ) * t₂ * Real.log z.1) * u =
          (z.2 : ℝ) * (t₁ + u * t₂) * Real.log z.1 by ring]
      ring
    _ = (∑' z : Nat.Primes × ℕ,
        fordEulerRawTerm eta (t₁ + u * t₂) z) *
          (1 / Real.cosh u ^ 2) := by
      rw [tsum_mul_right]
    _ = Real.log ‖riemannZeta (fordZetaLine eta (t₁ + u * t₂))‖ *
        (1 / Real.cosh u ^ 2) := by
      rw [tsum_fordEulerRawTerm_eq_log_norm heta]
    _ = Real.log ‖riemannZeta (fordZetaLine eta (t₁ + u * t₂))‖ /
        Real.cosh u ^ 2 := by ring

/-- Exact Fourier-series evaluation of the zeta-log integral. -/
theorem ford_integral_log_norm_zeta_eq_prime_power_fourier
    {eta : ℝ} (heta : 0 < eta) (t₁ t₂ : ℝ) :
    (∫ u : ℝ,
        Real.log ‖riemannZeta (fordZetaLine eta (t₁ + u * t₂))‖ /
          Real.cosh u ^ 2) =
      ∑' z : Nat.Primes × ℕ,
        fordPrimePowerWeight eta z.1 z.2 *
          fordFourierKernel ((z.2 : ℝ) * t₂ * Real.log z.1) *
          Real.cos ((z.2 : ℝ) * t₁ * Real.log z.1) := by
  rw [← integral_tsum_fordEulerFourierTerm heta]
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun u =>
    (tsum_fordEulerFourierTerm_eq_log_norm_div heta t₁ t₂ u).symm

noncomputable def fordTransformedFrequencyTerm
    (eta t₁ t₂ : ℝ) (j : ℕ) (z : Nat.Primes × ℕ) : ℝ :=
  fordPrimePowerWeight eta z.1 z.2 *
    fordFourierKernel ((z.2 : ℝ) * t₂ * Real.log z.1) *
    Real.cos ((z.2 : ℝ) * (j : ℝ) * t₁ * Real.log z.1)

theorem summable_fordTransformedFrequencyTerm
    {eta : ℝ} (heta : 0 < eta) (t₁ t₂ : ℝ) (j : ℕ) :
    Summable (fordTransformedFrequencyTerm eta t₁ t₂ j) := by
  apply Summable.of_norm
  refine ((summable_fordPrimePowerWeight heta).mul_left 2).of_nonneg_of_le
    (fun z => norm_nonneg (fordTransformedFrequencyTerm eta t₁ t₂ j z)) ?_
  intro z
  have hq := fordPrimePowerWeight_nonneg eta z.1 z.2
  have hU0 := fordFourierKernel_nonneg
    ((z.2 : ℝ) * t₂ * Real.log z.1)
  have hU2 := fordFourierKernel_le_two
    ((z.2 : ℝ) * t₂ * Real.log z.1)
  rw [fordTransformedFrequencyTerm, Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg hq, abs_of_nonneg hU0]
  have hCos := Real.abs_cos_le_one
    ((z.2 : ℝ) * (j : ℝ) * t₁ * Real.log z.1)
  calc
    fordPrimePowerWeight eta z.1 z.2 *
        fordFourierKernel ((z.2 : ℝ) * t₂ * Real.log z.1) *
        |Real.cos ((z.2 : ℝ) * (j : ℝ) * t₁ * Real.log z.1)| ≤
      fordPrimePowerWeight eta z.1 z.2 *
        fordFourierKernel ((z.2 : ℝ) * t₂ * Real.log z.1) * 1 :=
      mul_le_mul_of_nonneg_left hCos (mul_nonneg hq hU0)
    _ ≤ fordPrimePowerWeight eta z.1 z.2 * 2 :=
      by simpa only [mul_one] using mul_le_mul_of_nonneg_left hU2 hq
    _ = 2 * fordPrimePowerWeight eta z.1 z.2 := by ring

theorem ford_frequency_integral_eq_tsum
    {eta : ℝ} (heta : 0 < eta) (t₁ t₂ : ℝ) (j : ℕ) :
    (∫ u : ℝ,
        Real.log
          ‖riemannZeta
            (fordZetaLine eta ((j : ℝ) * t₁ + u * t₂))‖ /
          Real.cosh u ^ 2) =
      ∑' z : Nat.Primes × ℕ,
        fordTransformedFrequencyTerm eta t₁ t₂ j z := by
  rw [ford_integral_log_norm_zeta_eq_prime_power_fourier heta]
  apply tsum_congr
  intro z
  simp only [fordTransformedFrequencyTerm]
  rw [show (z.2 : ℝ) * ((j : ℝ) * t₁) * Real.log z.1 =
      (z.2 : ℝ) * (j : ℝ) * t₁ * Real.log z.1 by ring]

/-- Ford's literal four nonconstant frequencies on the left of Lemma 5.1,
written as a finite linear combination of the corresponding integrals. -/
noncomputable def fordLemma51Left
    (a₁ a₂ eta t₁ t₂ : ℝ) : ℝ :=
  fordTrigB1 a₁ a₂ *
      (∫ u : ℝ,
        Real.log ‖riemannZeta (fordZetaLine eta (t₁ + u * t₂))‖ /
          Real.cosh u ^ 2) +
    fordTrigB2 a₁ a₂ *
      (∫ u : ℝ,
        Real.log ‖riemannZeta (fordZetaLine eta (2 * t₁ + u * t₂))‖ /
          Real.cosh u ^ 2) +
    fordTrigB3 a₁ a₂ *
      (∫ u : ℝ,
        Real.log ‖riemannZeta (fordZetaLine eta (3 * t₁ + u * t₂))‖ /
          Real.cosh u ^ 2) +
    fordTrigB4 *
      (∫ u : ℝ,
        Real.log ‖riemannZeta (fordZetaLine eta (4 * t₁ + u * t₂))‖ /
          Real.cosh u ^ 2)

theorem fordLemma51Left_eq_transformed_tsum
    {eta : ℝ} (heta : 0 < eta) (a₁ a₂ t₁ t₂ : ℝ) :
    fordLemma51Left a₁ a₂ eta t₁ t₂ =
      ∑' z : Nat.Primes × ℕ,
        (fordTrigB1 a₁ a₂ * fordTransformedFrequencyTerm eta t₁ t₂ 1 z +
          fordTrigB2 a₁ a₂ * fordTransformedFrequencyTerm eta t₁ t₂ 2 z +
          fordTrigB3 a₁ a₂ * fordTransformedFrequencyTerm eta t₁ t₂ 3 z +
          fordTrigB4 * fordTransformedFrequencyTerm eta t₁ t₂ 4 z) := by
  have e1 :
      (∫ u : ℝ,
        Real.log ‖riemannZeta (fordZetaLine eta (t₁ + u * t₂))‖ /
          Real.cosh u ^ 2) =
        ∑' z : Nat.Primes × ℕ,
          fordTransformedFrequencyTerm eta t₁ t₂ 1 z := by
    convert ford_frequency_integral_eq_tsum heta t₁ t₂ 1 using 1
    norm_num
  have e2 :
      (∫ u : ℝ,
        Real.log ‖riemannZeta (fordZetaLine eta (2 * t₁ + u * t₂))‖ /
          Real.cosh u ^ 2) =
        ∑' z : Nat.Primes × ℕ,
          fordTransformedFrequencyTerm eta t₁ t₂ 2 z := by
    exact ford_frequency_integral_eq_tsum heta t₁ t₂ 2
  have e3 :
      (∫ u : ℝ,
        Real.log ‖riemannZeta (fordZetaLine eta (3 * t₁ + u * t₂))‖ /
          Real.cosh u ^ 2) =
        ∑' z : Nat.Primes × ℕ,
          fordTransformedFrequencyTerm eta t₁ t₂ 3 z := by
    exact ford_frequency_integral_eq_tsum heta t₁ t₂ 3
  have e4 :
      (∫ u : ℝ,
        Real.log ‖riemannZeta (fordZetaLine eta (4 * t₁ + u * t₂))‖ /
          Real.cosh u ^ 2) =
        ∑' z : Nat.Primes × ℕ,
          fordTransformedFrequencyTerm eta t₁ t₂ 4 z := by
    exact ford_frequency_integral_eq_tsum heta t₁ t₂ 4
  rw [fordLemma51Left, e1, e2, e3, e4]
  have s1 := summable_fordTransformedFrequencyTerm heta t₁ t₂ 1
  have s2 := summable_fordTransformedFrequencyTerm heta t₁ t₂ 2
  have s3 := summable_fordTransformedFrequencyTerm heta t₁ t₂ 3
  have s4 := summable_fordTransformedFrequencyTerm heta t₁ t₂ 4
  have h1 := s1.mul_left (fordTrigB1 a₁ a₂)
  have h2 := s2.mul_left (fordTrigB2 a₁ a₂)
  have h3 := s3.mul_left (fordTrigB3 a₁ a₂)
  have h4 := s4.mul_left fordTrigB4
  rw [← s1.tsum_mul_left (fordTrigB1 a₁ a₂),
    ← s2.tsum_mul_left (fordTrigB2 a₁ a₂),
    ← s3.tsum_mul_left (fordTrigB3 a₁ a₂),
    ← s4.tsum_mul_left fordTrigB4,
    ← h1.tsum_add h2, ← (h1.add h2).tsum_add h3,
    ← ((h1.add h2).add h3).tsum_add h4]

theorem ford_transformed_frequency_combination
    (a₁ a₂ eta t₁ t₂ : ℝ) (z : Nat.Primes × ℕ) :
    fordTrigB1 a₁ a₂ * fordTransformedFrequencyTerm eta t₁ t₂ 1 z +
        fordTrigB2 a₁ a₂ * fordTransformedFrequencyTerm eta t₁ t₂ 2 z +
        fordTrigB3 a₁ a₂ * fordTransformedFrequencyTerm eta t₁ t₂ 3 z +
        fordTrigB4 * fordTransformedFrequencyTerm eta t₁ t₂ 4 z =
      fordPrimePowerWeight eta z.1 z.2 *
        fordFourierKernel ((z.2 : ℝ) * t₂ * Real.log z.1) *
        fordTrigOscillatory a₁ a₂
          ((z.2 : ℝ) * t₁ * Real.log z.1) := by
  simp only [fordTransformedFrequencyTerm, fordTrigOscillatory]
  have h1 : Real.cos ((z.2 : ℝ) * ((1 : ℕ) : ℝ) * t₁ * Real.log z.1) =
      Real.cos ((z.2 : ℝ) * t₁ * Real.log z.1) := by
    congr 1
    norm_num
  have h2 : Real.cos ((z.2 : ℝ) * ((2 : ℕ) : ℝ) * t₁ * Real.log z.1) =
      Real.cos (2 * ((z.2 : ℝ) * t₁ * Real.log z.1)) := by
    congr 1
    norm_num
    ring
  have h3 : Real.cos ((z.2 : ℝ) * ((3 : ℕ) : ℝ) * t₁ * Real.log z.1) =
      Real.cos (3 * ((z.2 : ℝ) * t₁ * Real.log z.1)) := by
    congr 1
    norm_num
    ring
  have h4 : Real.cos ((z.2 : ℝ) * ((4 : ℕ) : ℝ) * t₁ * Real.log z.1) =
      Real.cos (4 * ((z.2 : ℝ) * t₁ * Real.log z.1)) := by
    congr 1
    norm_num
    ring
  rw [h1, h2, h3, h4]
  ring

noncomputable def fordOscillatoryPrimePowerTerm
    (a₁ a₂ eta t₁ t₂ : ℝ) (z : Nat.Primes × ℕ) : ℝ :=
  fordPrimePowerWeight eta z.1 z.2 *
    fordFourierKernel ((z.2 : ℝ) * t₂ * Real.log z.1) *
    fordTrigOscillatory a₁ a₂ ((z.2 : ℝ) * t₁ * Real.log z.1)

theorem summable_fordOscillatoryPrimePowerTerm
    {eta : ℝ} (heta : 0 < eta) (a₁ a₂ t₁ t₂ : ℝ) :
    Summable (fordOscillatoryPrimePowerTerm a₁ a₂ eta t₁ t₂) := by
  have h1 := (summable_fordTransformedFrequencyTerm heta t₁ t₂ 1).mul_left
    (fordTrigB1 a₁ a₂)
  have h2 := (summable_fordTransformedFrequencyTerm heta t₁ t₂ 2).mul_left
    (fordTrigB2 a₁ a₂)
  have h3 := (summable_fordTransformedFrequencyTerm heta t₁ t₂ 3).mul_left
    (fordTrigB3 a₁ a₂)
  have h4 := (summable_fordTransformedFrequencyTerm heta t₁ t₂ 4).mul_left
    fordTrigB4
  exact (((h1.add h2).add h3).add h4).congr fun z => by
    simpa only [fordOscillatoryPrimePowerTerm] using
      ford_transformed_frequency_combination a₁ a₂ eta t₁ t₂ z

theorem fordLemma51Left_eq_oscillatory_tsum
    {eta : ℝ} (heta : 0 < eta) (a₁ a₂ t₁ t₂ : ℝ) :
    fordLemma51Left a₁ a₂ eta t₁ t₂ =
      ∑' z : Nat.Primes × ℕ,
        fordOscillatoryPrimePowerTerm a₁ a₂ eta t₁ t₂ z := by
  rw [fordLemma51Left_eq_transformed_tsum heta]
  apply tsum_congr
  intro z
  exact ford_transformed_frequency_combination a₁ a₂ eta t₁ t₂ z

noncomputable def fordLowerPrimePowerTerm
    (a₁ a₂ eta t₂ : ℝ) (z : Nat.Primes × ℕ) : ℝ :=
  -fordTrigB0 a₁ a₂ *
    (fordPrimePowerWeight eta z.1 z.2 *
      fordFourierKernel ((z.2 : ℝ) * t₂ * Real.log z.1))

theorem fordLowerPrimePowerTerm_le_oscillatory
    (a₁ a₂ eta t₁ t₂ : ℝ) (z : Nat.Primes × ℕ) :
    fordLowerPrimePowerTerm a₁ a₂ eta t₂ z ≤
      fordOscillatoryPrimePowerTerm a₁ a₂ eta t₁ t₂ z := by
  simpa only [fordLowerPrimePowerTerm, fordOscillatoryPrimePowerTerm] using
    ford_weighted_trigonometric_lower a₁ a₂
      ((z.2 : ℝ) * t₁ * Real.log z.1)
      (fordPrimePowerWeight eta z.1 z.2)
      (fordFourierKernel ((z.2 : ℝ) * t₂ * Real.log z.1))
      (fordPrimePowerWeight_nonneg eta z.1 z.2)
      (fordFourierKernel_nonneg _)

theorem summable_fordLowerPrimePowerTerm
    {eta : ℝ} (heta : 0 < eta) (a₁ a₂ t₂ : ℝ) :
    Summable (fordLowerPrimePowerTerm a₁ a₂ eta t₂) := by
  apply Summable.of_norm
  refine ((summable_fordPrimePowerWeight heta).mul_left
    (2 * fordTrigB0 a₁ a₂)).of_nonneg_of_le
      (fun z => norm_nonneg (fordLowerPrimePowerTerm a₁ a₂ eta t₂ z)) ?_
  intro z
  have hb := (fordTrigB0_pos a₁ a₂).le
  have hq := fordPrimePowerWeight_nonneg eta z.1 z.2
  have hU0 := fordFourierKernel_nonneg
    ((z.2 : ℝ) * t₂ * Real.log z.1)
  have hU2 := fordFourierKernel_le_two
    ((z.2 : ℝ) * t₂ * Real.log z.1)
  rw [fordLowerPrimePowerTerm, Real.norm_eq_abs, abs_mul, abs_neg,
    abs_of_nonneg hb, abs_mul, abs_of_nonneg hq, abs_of_nonneg hU0]
  calc
    fordTrigB0 a₁ a₂ *
        (fordPrimePowerWeight eta z.1 z.2 *
          fordFourierKernel ((z.2 : ℝ) * t₂ * Real.log z.1)) =
      (fordTrigB0 a₁ a₂ * fordPrimePowerWeight eta z.1 z.2) *
        fordFourierKernel ((z.2 : ℝ) * t₂ * Real.log z.1) := by ring
    _ ≤ (fordTrigB0 a₁ a₂ * fordPrimePowerWeight eta z.1 z.2) * 2 :=
      mul_le_mul_of_nonneg_left hU2 (mul_nonneg hb hq)
    _ = 2 * fordTrigB0 a₁ a₂ * fordPrimePowerWeight eta z.1 z.2 := by ring

theorem tsum_fordLowerPrimePowerTerm_le_left
    {eta : ℝ} (heta : 0 < eta) (a₁ a₂ t₁ t₂ : ℝ) :
    (∑' z : Nat.Primes × ℕ, fordLowerPrimePowerTerm a₁ a₂ eta t₂ z) ≤
      fordLemma51Left a₁ a₂ eta t₁ t₂ := by
  rw [fordLemma51Left_eq_oscillatory_tsum heta]
  exact Summable.tsum_le_tsum
    (fordLowerPrimePowerTerm_le_oscillatory a₁ a₂ eta t₁ t₂)
    (summable_fordLowerPrimePowerTerm heta a₁ a₂ t₂)
    (summable_fordOscillatoryPrimePowerTerm heta a₁ a₂ t₁ t₂)

theorem tsum_prod_fordPrimePowerWeight
    {eta : ℝ} (heta : 0 < eta) :
    (∑' z : Nat.Primes × ℕ, fordPrimePowerWeight eta z.1 z.2) =
      Real.log ‖riemannZeta (fordZetaLine eta 0)‖ := by
  have h := summable_fordPrimePowerWeight heta
  rw [h.tsum_prod' (fun p => h.prod_factor p),
    tsum_fordPrimePowerWeight heta]

theorem ford_constant_lower_le_lowerTerm
    (a₁ a₂ eta t₂ : ℝ) (z : Nat.Primes × ℕ) :
    -2 * fordTrigB0 a₁ a₂ * fordPrimePowerWeight eta z.1 z.2 ≤
      fordLowerPrimePowerTerm a₁ a₂ eta t₂ z := by
  have hb := (fordTrigB0_pos a₁ a₂).le
  have hq := fordPrimePowerWeight_nonneg eta z.1 z.2
  have hU := fordFourierKernel_le_two
    ((z.2 : ℝ) * t₂ * Real.log z.1)
  simp only [fordLowerPrimePowerTerm]
  calc
    -2 * fordTrigB0 a₁ a₂ * fordPrimePowerWeight eta z.1 z.2 =
        -((fordTrigB0 a₁ a₂ * fordPrimePowerWeight eta z.1 z.2) * 2) := by ring
    _ ≤ -((fordTrigB0 a₁ a₂ * fordPrimePowerWeight eta z.1 z.2) *
        fordFourierKernel ((z.2 : ℝ) * t₂ * Real.log z.1)) :=
      neg_le_neg (mul_le_mul_of_nonneg_left hU (mul_nonneg hb hq))
    _ = -fordTrigB0 a₁ a₂ *
        (fordPrimePowerWeight eta z.1 z.2 *
          fordFourierKernel ((z.2 : ℝ) * t₂ * Real.log z.1)) := by ring

theorem ford_constant_lower_le_lower_tsum
    {eta : ℝ} (heta : 0 < eta) (a₁ a₂ t₂ : ℝ) :
    -2 * fordTrigB0 a₁ a₂ *
        Real.log ‖riemannZeta (fordZetaLine eta 0)‖ ≤
      ∑' z : Nat.Primes × ℕ,
        fordLowerPrimePowerTerm a₁ a₂ eta t₂ z := by
  have hWeight := summable_fordPrimePowerWeight heta
  have hConst := hWeight.mul_left
    (-2 * fordTrigB0 a₁ a₂)
  have hLower := summable_fordLowerPrimePowerTerm heta a₁ a₂ t₂
  have h := Summable.tsum_le_tsum
    (ford_constant_lower_le_lowerTerm a₁ a₂ eta t₂) hConst hLower
  have hEq :
      (∑' z : Nat.Primes × ℕ,
        -2 * fordTrigB0 a₁ a₂ * fordPrimePowerWeight eta z.1 z.2) =
        -2 * fordTrigB0 a₁ a₂ *
          Real.log ‖riemannZeta (fordZetaLine eta 0)‖ := by
    rw [hWeight.tsum_mul_left, tsum_prod_fordPrimePowerWeight heta]
  rw [hEq] at h
  exact h

/-- The positive real value `ζ(1+eta)` occurring on the right of Ford's
Lemma 5.1. -/
noncomputable def fordRealZetaValue (eta : ℝ) : ℝ :=
  (riemannZeta (((1 + eta : ℝ) : ℂ))).re

theorem fordRealZetaValue_pos {eta : ℝ} (heta : 0 < eta) :
    0 < fordRealZetaValue eta := by
  exact riemannZeta_re_pos_of_one_lt (by linarith)

theorem norm_riemannZeta_fordLine_zero
    {eta : ℝ} (heta : 0 < eta) :
    ‖riemannZeta (fordZetaLine eta 0)‖ = fordRealZetaValue eta := by
  have hIm := riemannZeta_im_eq_zero_of_one_lt
    (show (1 : ℝ) < 1 + eta by linarith)
  have hEq : riemannZeta (((1 + eta : ℝ) : ℂ)) =
      ((fordRealZetaValue eta : ℝ) : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using hIm
  rw [show fordZetaLine eta 0 = (((1 + eta : ℝ) : ℂ)) by
    simp [fordZetaLine], hEq, Complex.norm_real,
    Real.norm_of_nonneg (fordRealZetaValue_pos heta).le]

/-- Ford, Lemma 5.1, with the four source coefficients and the literal
`1/cosh² u` weight. -/
theorem ford_lemma_5_1
    {eta : ℝ} (heta : 0 < eta) (a₁ a₂ t₁ t₂ : ℝ) :
    -2 * fordTrigB0 a₁ a₂ * Real.log (fordRealZetaValue eta) ≤
      fordLemma51Left a₁ a₂ eta t₁ t₂ := by
  rw [← norm_riemannZeta_fordLine_zero heta]
  exact (ford_constant_lower_le_lower_tsum heta a₁ a₂ t₂).trans
    (tsum_fordLowerPrimePowerTerm_le_left heta a₁ a₂ t₁ t₂)

end GafniTao
