import Tao2026.LowFrequency
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Low-frequency discrete-to-continuous bridge

This module isolates the elementary part of the classical-PNT branch in
Tao's Proposition 1.12.  It compares the logarithmically weighted integer
reciprocal-phase sum with the corresponding interval integral.  No prime
number theorem input is used here.
-/

open Complex Finset MeasureTheory Set
open scoped BigOperators

namespace Tao2026

noncomputable section

/-- An interval integral with natural endpoints is the exact sum of its
unit-cell interval integrals. -/
theorem sum_Ico_intervalIntegral_nat_cells_complex
    (f : ℝ → ℂ)
    (hf : ∀ a b : ℝ, IntervalIntegrable f volume a b)
    {a b : ℕ} (hab : a ≤ b) :
    (∑ n ∈ Finset.Ico a b,
        ∫ t in (n : ℝ)..(n + 1 : ℝ), f t) =
      ∫ t in (a : ℝ)..(b : ℝ), f t := by
  induction b with
  | zero =>
      have ha : a = 0 := by omega
      subst a
      simp
  | succ b ih =>
      by_cases hab' : a ≤ b
      · rw [Finset.sum_Ico_succ_top hab', ih hab',
          intervalIntegral.integral_add_adjacent_intervals
            (hf (a : ℝ) (b : ℝ)) (hf (b : ℝ) (b + 1 : ℝ))]
        norm_num
      · have ha : a = b + 1 := by omega
        subst a
        simp

/-- The inverse logarithm has a uniform Lipschitz constant on a positive
dyadic interval. -/
theorem abs_inv_log_sub_le_dyadic
    {P s t : ℝ} (hP : 2 ≤ P)
    (hs : s ∈ Set.Icc P (2 * P)) (ht : t ∈ Set.Icc P (2 * P)) :
    |(Real.log t)⁻¹ - (Real.log s)⁻¹| ≤
      (1 / (P * (Real.log P) ^ 2)) * |t - s| := by
  have hPpos : 0 < P := by linarith
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hdiff : ∀ x ∈ Set.Icc P (2 * P),
      DifferentiableAt ℝ (fun y : ℝ => (Real.log y)⁻¹) x := by
    intro x hx
    have hxpos : 0 < x := hPpos.trans_le hx.1
    have hxone : 1 < x := (by norm_num : (1 : ℝ) < 2).trans_le (hP.trans hx.1)
    exact ((Real.hasDerivAt_log hxpos.ne').inv
      (ne_of_gt (Real.log_pos hxone))).differentiableAt
  have hbound : ∀ x ∈ Set.Icc P (2 * P),
      ‖deriv (fun y : ℝ => (Real.log y)⁻¹) x‖ ≤
        1 / (P * (Real.log P) ^ 2) := by
    intro x hx
    have hxpos : 0 < x := hPpos.trans_le hx.1
    have hxone : 1 < x := (by norm_num : (1 : ℝ) < 2).trans_le (hP.trans hx.1)
    have hlogx : 0 < Real.log x := Real.log_pos hxone
    have hlogPx : Real.log P ≤ Real.log x :=
      Real.log_le_log hPpos hx.1
    have hderiv := (Real.hasDerivAt_log hxpos.ne').inv hlogx.ne'
    have hderiv' : deriv (fun y : ℝ => (Real.log y)⁻¹) x =
        -x⁻¹ / Real.log x ^ 2 := hderiv.deriv
    rw [hderiv', Real.norm_eq_abs, abs_div, abs_neg,
      abs_inv, abs_of_pos hxpos, abs_pow, abs_of_pos hlogx,
      one_div]
    rw [div_eq_mul_inv, ← mul_inv]
    apply inv_anti₀
    · positivity
    · exact mul_le_mul hx.1 (pow_le_pow_left₀ hlogP.le hlogPx 2)
        (sq_nonneg _) hxpos.le
  simpa [Real.norm_eq_abs] using
    (Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound
      (convex_Icc P (2 * P)) hs ht)

/-- On a positive dyadic interval, the logarithmically weighted reciprocal
character varies by the phase variation plus the inverse-logarithm
variation. -/
theorem norm_reciprocalPhaseLogWeight_sub_le_dyadic
    (N M : ℝ) {j : ℕ} (hj : 1 ≤ j) {P s t : ℝ} (hP : 2 ≤ P)
    (hs : s ∈ Set.Icc P (2 * P)) (ht : t ∈ Set.Icc P (2 * P)) :
    ‖standardAdditiveCharacter (reciprocalPhase N M j t) / Real.log t -
        standardAdditiveCharacter (reciprocalPhase N M j s) / Real.log s‖ ≤
      (2 * Real.pi *
          ((j + 1 : ℕ) * reciprocalPhaseScale N M j P / P) /
          Real.log P +
        1 / (P * (Real.log P) ^ 2)) * |t - s| := by
  have hPpos : 0 < P := by linarith
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have htpos : 0 < t := hPpos.trans_le ht.1
  have hlogt : 0 < Real.log t := Real.log_pos
    ((by norm_num : (1 : ℝ) < 2).trans_le (hP.trans ht.1))
  have hlogPt : Real.log P ≤ Real.log t := Real.log_le_log hPpos ht.1
  let zt := standardAdditiveCharacter (reciprocalPhase N M j t)
  let zs := standardAdditiveCharacter (reciprocalPhase N M j s)
  have hchar : ‖zt - zs‖ ≤
      2 * Real.pi *
        (((j + 1 : ℕ) * reciprocalPhaseScale N M j P / P) * |t - s|) := by
    simpa only [zt, zs] using
      norm_standardAdditiveCharacter_reciprocalPhase_sub_le
        N M hj hPpos hs ht
  have hloginv : |(Real.log t)⁻¹ - (Real.log s)⁻¹| ≤
      (1 / (P * (Real.log P) ^ 2)) * |t - s| :=
    abs_inv_log_sub_le_dyadic hP hs ht
  have hinv : (Real.log t)⁻¹ ≤ (Real.log P)⁻¹ :=
    inv_anti₀ hlogP hlogPt
  have hdecomp :
      zt / (Real.log t : ℂ) - zs / (Real.log s : ℂ) =
        (zt - zs) * ((Real.log t : ℂ)⁻¹) +
          zs * (((Real.log t)⁻¹ - (Real.log s)⁻¹ : ℝ) : ℂ) := by
    push_cast
    field_simp
    ring
  change ‖zt / (Real.log t : ℂ) - zs / (Real.log s : ℂ)‖ ≤ _
  rw [hdecomp]
  calc
    ‖(zt - zs) * ((Real.log t : ℂ)⁻¹) +
        zs * (((Real.log t)⁻¹ - (Real.log s)⁻¹ : ℝ) : ℂ)‖ ≤
        ‖zt - zs‖ * (Real.log t)⁻¹ +
          |(Real.log t)⁻¹ - (Real.log s)⁻¹| := by
      calc
        _ ≤ ‖(zt - zs) * ((Real.log t : ℂ)⁻¹)‖ +
              ‖zs * (((Real.log t)⁻¹ - (Real.log s)⁻¹ : ℝ) : ℂ)‖ :=
          norm_add_le _ _
        _ = _ := by
          simp [norm_mul, zt, zs, norm_standardAdditiveCharacter,
            norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlogt]
    _ ≤ (2 * Real.pi *
          (((j + 1 : ℕ) * reciprocalPhaseScale N M j P / P) * |t - s|)) *
          (Real.log P)⁻¹ +
        (1 / (P * (Real.log P) ^ 2)) * |t - s| := by
      exact add_le_add
        (mul_le_mul hchar hinv (inv_nonneg.mpr hlogt.le) (norm_nonneg _))
        hloginv
    _ = (2 * Real.pi *
          ((j + 1 : ℕ) * reciprocalPhaseScale N M j P / P) /
          Real.log P +
        1 / (P * (Real.log P) ^ 2)) * |t - s| := by
      rw [div_eq_mul_inv]
      ring

end

end Tao2026
