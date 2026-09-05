import GafniTao.PintzZetaAFETailKernel

/-!
# Integrated displaced edges for the single-zeta AFE

The all-height pointwise estimates are integrated here.  Both Gaussian
masses are evaluated by Mathlib's proved Gaussian integral, and the
normalizing factor `1/(2*pi)` is retained explicitly.
-/

open Complex MeasureTheory Set
open scoped Interval

namespace GafniTao

noncomputable section

/-- A finite symmetric interval contains no more Gaussian mass than the
whole real line. -/
theorem intervalIntegral_exp_neg_mul_sq_le_gaussian
    {b H : ℝ} (hb : 0 < b) (hH : 0 ≤ H) :
    ∫ u in -H..H, Real.exp (-b * u ^ 2) ≤ Real.sqrt (Real.pi / b) := by
  have hInt : Integrable (fun u : ℝ => Real.exp (-b * u ^ 2)) :=
    integrable_exp_neg_mul_sq hb
  rw [intervalIntegral.integral_of_le (by linarith)]
  calc
    ∫ u in Set.Ioc (-H) H, Real.exp (-b * u ^ 2) ≤
        ∫ u : ℝ, Real.exp (-b * u ^ 2) :=
      MeasureTheory.setIntegral_le_integral hInt
        (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
    _ = Real.sqrt (Real.pi / b) := integral_gaussian b

/-- A two-Gaussian pointwise majorant integrates with the corresponding
two exact Gaussian masses. -/
theorem norm_intervalIntegral_le_gaussian_pair
    {f : ℝ → ℂ} {A B H : ℝ} (hH : 0 ≤ H)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hpoint : ∀ u : ℝ, ‖f u‖ ≤
      A * Real.exp (-50 * u ^ 2) + B * Real.exp (-25 * u ^ 2)) :
    ‖∫ u in -H..H, f u‖ ≤
      A * Real.sqrt (Real.pi / 50) + B * Real.sqrt (Real.pi / 25) := by
  let g : ℝ → ℝ := fun u =>
    A * Real.exp (-50 * u ^ 2) + B * Real.exp (-25 * u ^ 2)
  have hInt50 : Integrable (fun u : ℝ => Real.exp (-50 * u ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num)
  have hInt25 : Integrable (fun u : ℝ => Real.exp (-25 * u ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num)
  have hgInt : Integrable g := (hInt50.const_mul A).add (hInt25.const_mul B)
  have hgInterval : IntervalIntegrable g volume (-H) H := hgInt.intervalIntegrable
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le
    (show -H ≤ H by linarith)
    (Filter.Eventually.of_forall fun u _hu => hpoint u) hgInterval
  calc
    ‖∫ u in -H..H, f u‖ ≤ ∫ u in -H..H, g u := hnorm
    _ = A * (∫ u in -H..H, Real.exp (-50 * u ^ 2)) +
        B * (∫ u in -H..H, Real.exp (-25 * u ^ 2)) := by
      dsimp only [g]
      rw [intervalIntegral.integral_add
        (hInt50.const_mul A).intervalIntegrable
        (hInt25.const_mul B).intervalIntegrable,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
    _ ≤ A * Real.sqrt (Real.pi / 50) +
        B * Real.sqrt (Real.pi / 25) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          (intervalIntegral_exp_neg_mul_sq_le_gaussian (by norm_num) hH) hA)
        (mul_le_mul_of_nonneg_left
          (intervalIntegral_exp_neg_mul_sq_le_gaussian (by norm_num) hH) hB)

/-- Integrated original displaced coefficient. -/
theorem exists_norm_pintzZetaAFETermVerticalTrunc_original_left_le
    {r q : ℝ} (hrLower : 1 / 2 < r) (hrUpper : r < 1)
    (hq : 0 < q) (hqr : q < r) :
    ∃ Ccentral Ctail : ℝ, 0 < Ccentral ∧ 0 < Ctail ∧
      ∀ (t H : ℝ) (n : ℕ), 4 ≤ t → 0 ≤ H → n ≠ 0 →
      ‖pintzZetaAFETermVerticalTrunc
          (((r : ℝ) : ℂ) + (t : ℂ) * I)
          (((r : ℝ) : ℂ) + (t : ℂ) * I) n (-q) H‖ ≤
        (1 / (2 * Real.pi)) *
          (Ccentral * Real.exp (-Real.log (t / 4 + 2) * (q / 2)) *
              (n : ℝ) ^ (-(r - q)) * Real.sqrt (Real.pi / 50) +
            Ctail * Real.exp (-10 * t ^ 2) * Real.sqrt (Real.pi / 25)) := by
  obtain ⟨Ccentral, Ctail, hCcentral, hCtail, hpoint⟩ :=
    exists_norm_pintzZetaAFETerm_original_all_height_le
      hrLower hrUpper hq hqr
  refine ⟨Ccentral, Ctail, hCcentral, hCtail, ?_⟩
  intro t H n ht hH hn
  let A : ℝ := Ccentral *
    Real.exp (-Real.log (t / 4 + 2) * (q / 2)) *
    (n : ℝ) ^ (-(r - q))
  let B : ℝ := Ctail * Real.exp (-10 * t ^ 2)
  have hIntegral := norm_intervalIntegral_le_gaussian_pair hH
    (show 0 ≤ A by dsimp only [A]; positivity)
    (show 0 ≤ B by dsimp only [B]; positivity)
    (fun u => by
      dsimp only [A, B]
      refine (hpoint t u n ht hn).trans_eq ?_
      ring)
  unfold pintzZetaAFETermVerticalTrunc
  rw [norm_mul, norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
  exact mul_le_mul_of_nonneg_left (by simpa only [A, B, mul_assoc] using hIntegral)
    (by positivity)

/-- Integrated reflected displaced coefficient. -/
theorem exists_norm_pintzZetaAFETermVerticalTrunc_dual_left_le
    {r q : ℝ} (hrLower : 1 / 2 < r) (hrUpper : r < 1)
    (hq : 0 < q) (hqDual : q < 1 - r) :
    ∃ Ccentral Ctail : ℝ, 0 < Ccentral ∧ 0 < Ctail ∧
      ∀ (t H : ℝ) (n : ℕ), 4 ≤ t → 0 ≤ H → n ≠ 0 →
      ‖pintzZetaAFETermVerticalTrunc
          (((r : ℝ) : ℂ) + (t : ℂ) * I)
          (1 - (((r : ℝ) : ℂ) + (t : ℂ) * I)) n (-q) H‖ ≤
        (1 / (2 * Real.pi)) *
          (Ccentral * Real.exp (-Real.log (t / 4 + 2) * (q / 2)) *
              Real.exp (Real.log (t / 4 + 2) * (1 / 2 - r)) *
              (n : ℝ) ^ (-(1 - r - q)) * Real.sqrt (Real.pi / 50) +
            Ctail * Real.exp (-10 * t ^ 2) * Real.sqrt (Real.pi / 25)) := by
  obtain ⟨Ccentral, Ctail, hCcentral, hCtail, hpoint⟩ :=
    exists_norm_pintzZetaAFETerm_dual_all_height_le
      hrLower hrUpper hq hqDual
  refine ⟨Ccentral, Ctail, hCcentral, hCtail, ?_⟩
  intro t H n ht hH hn
  let A : ℝ := Ccentral *
    Real.exp (-Real.log (t / 4 + 2) * (q / 2)) *
    Real.exp (Real.log (t / 4 + 2) * (1 / 2 - r)) *
    (n : ℝ) ^ (-(1 - r - q))
  let B : ℝ := Ctail * Real.exp (-10 * t ^ 2)
  have hIntegral := norm_intervalIntegral_le_gaussian_pair hH
    (show 0 ≤ A by dsimp only [A]; positivity)
    (show 0 ≤ B by dsimp only [B]; positivity)
    (fun u => by
      dsimp only [A, B]
      refine (hpoint t u n ht hn).trans_eq ?_
      ring)
  unfold pintzZetaAFETermVerticalTrunc
  rw [norm_mul, norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
  exact mul_le_mul_of_nonneg_left (by simpa only [A, B, mul_assoc] using hIntegral)
    (by positivity)

#print axioms intervalIntegral_exp_neg_mul_sq_le_gaussian
#print axioms norm_intervalIntegral_le_gaussian_pair
#print axioms exists_norm_pintzZetaAFETermVerticalTrunc_original_left_le
#print axioms exists_norm_pintzZetaAFETermVerticalTrunc_dual_left_le

end

end GafniTao
