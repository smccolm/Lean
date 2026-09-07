import GafniTao.SharpPerronHorizontalPositive

/-!
# Transport to the physical zeta logarithmic derivative

The affine Landau coordinate has derivative `7/4`.  This file proves that
factor in Lean and returns the logarithmic-square estimate to the actual
Riemann zeta function on the positive Perron edge.
-/

open Complex Set Metric Finset
open RiemannZeta.GuthMaynard

noncomputable section

namespace GafniTao

theorem deriv_sharpLandauMap (T : ℝ) (w : ℂ) :
    deriv (sharpLandauMap T) w = (7 / 4 : ℝ) := by
  unfold sharpLandauMap
  simp

theorem logDeriv_sharpLandauNormalized_eq
    {T : ℝ} {w : ℂ}
    (hmapOne : sharpLandauMap T w ≠ 1)
    (hzeta : riemannZeta (sharpLandauMap T w) ≠ 0) :
    deriv (sharpLandauNormalized T) w / sharpLandauNormalized T w =
      (7 / 4 : ℝ) *
        (deriv riemannZeta (sharpLandauMap T w) /
          riemannZeta (sharpLandauMap T w)) := by
  have hmapDiff : DifferentiableAt ℂ (sharpLandauMap T) w := by
    unfold sharpLandauMap
    fun_prop
  have hzetaDiff : DifferentiableAt ℂ riemannZeta (sharpLandauMap T w) :=
    (analyticAt_riemannZeta hmapOne).differentiableAt
  have hcompDiff : DifferentiableAt ℂ (fun z ↦ riemannZeta (sharpLandauMap T z)) w :=
    hzetaDiff.comp w hmapDiff
  change deriv (fun z ↦ (riemannZeta (sharpLandauCenter T))⁻¹ *
      riemannZeta (sharpLandauMap T z)) w /
      ((riemannZeta (sharpLandauCenter T))⁻¹ *
        riemannZeta (sharpLandauMap T w)) = _
  rw [deriv_const_mul (riemannZeta (sharpLandauCenter T))⁻¹ hcompDiff]
  have hderivComp :
      deriv (fun z ↦ riemannZeta (sharpLandauMap T z)) w =
        deriv riemannZeta (sharpLandauMap T w) * deriv (sharpLandauMap T) w := by
    simpa only [Function.comp_apply] using
      (deriv_comp w hzetaDiff hmapDiff)
  rw [hderivComp, deriv_sharpLandauMap]
  have hcenter : (riemannZeta (sharpLandauCenter T))⁻¹ ≠ 0 :=
    inv_ne_zero (sharpLandauCenter_ne_zero T)
  field_simp
  calc
    riemannZeta (sharpLandauCenter T) *
          deriv riemannZeta (sharpLandauMap T w) *
            (riemannZeta (sharpLandauCenter T))⁻¹ =
        deriv riemannZeta (sharpLandauMap T w) *
          (riemannZeta (sharpLandauCenter T) *
            (riemannZeta (sharpLandauCenter T))⁻¹) := by ring
    _ = deriv riemannZeta (sharpLandauMap T w) := by
      rw [mul_inv_cancel₀ (sharpLandauCenter_ne_zero T), mul_one]

theorem sharpLandau_physical_point_ne_one
    {T σ R : ℝ} (hR : R ∈ Set.Icc T (T + 1)) (hT : 8 ≤ T) :
    sharpLandauMap T (sharpLandauCoord T σ R) ≠ 1 := by
  rw [sharpLandauMap_coord]
  intro h
  have him := congrArg Complex.im h
  simp at him
  linarith [hR.1]

theorem sharpLandau_physical_zeta_ne_zero
    {T σ R : ℝ} (hT : 8 ≤ T)
    (hR : R ∈ Set.Icc T (T + 1)) (hσ : σ ∈ Set.Icc (1 / 2) 2)
    (hfar : ∀ ρ ∈ sharpLandauZeroFinset T hT,
      1 / (2 * (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1)) ≤
        |R - (sharpLandauMap T ρ).im|) :
    riemannZeta (sharpLandauMap T (sharpLandauCoord T σ R)) ≠ 0 := by
  intro hz
  have hnorm := norm_sharpLandauCoord_le hR hσ
  have hzeroNorm : sharpLandauNormalized T (sharpLandauCoord T σ R) = 0 := by
    rw [sharpLandauNormalized, hz, mul_zero]
  exact sharpLandauCoord_not_mem_large_zeros hT hR hσ hfar
    ⟨hnorm.trans (by norm_num), hzeroNorm⟩

theorem norm_riemannZeta_logDeriv_positive_horizontal_le
    {T σ R : ℝ} (hT : 8 ≤ T)
    (hR : R ∈ Set.Icc T (T + 1)) (hσ : σ ∈ Set.Icc (1 / 2) 2)
    (hfar : ∀ ρ ∈ sharpLandauZeroFinset T hT,
      1 / (2 * (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1)) ≤
        |R - (sharpLandauMap T ρ).im|) :
    ‖deriv riemannZeta ((σ : ℂ) + (R : ℂ) * Complex.I) /
        riemannZeta ((σ : ℂ) + (R : ℂ) * Complex.I)‖ ≤
      (4 / 7 : ℝ) *
        (202 * sharpLandauPartialFractionConstant +
          (7 / 2 : ℝ) * (sharpLandauMassConstant + 1) *
            sharpLandauMassConstant) * Real.log T ^ 2 := by
  have hnorm := norm_sharpLandauNormalized_logDeriv_le_log_sq hT hR hσ hfar
  have heq := logDeriv_sharpLandauNormalized_eq
    (sharpLandau_physical_point_ne_one hR hT)
    (sharpLandau_physical_zeta_ne_zero hT hR hσ hfar)
  rw [sharpLandauMap_coord] at heq
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 4)] at hnorm
  calc
    ‖deriv riemannZeta ((σ : ℂ) + (R : ℂ) * Complex.I) /
        riemannZeta ((σ : ℂ) + (R : ℂ) * Complex.I)‖ =
        (4 / 7 : ℝ) * ((7 / 4 : ℝ) *
          ‖deriv riemannZeta ((σ : ℂ) + (R : ℂ) * Complex.I) /
            riemannZeta ((σ : ℂ) + (R : ℂ) * Complex.I)‖) := by ring
    _ ≤ (4 / 7 : ℝ) *
        ((202 * sharpLandauPartialFractionConstant +
          (7 / 2 : ℝ) * (sharpLandauMassConstant + 1) *
            sharpLandauMassConstant) * Real.log T ^ 2) := by
      exact mul_le_mul_of_nonneg_left hnorm (by norm_num)
    _ = (4 / 7 : ℝ) *
        (202 * sharpLandauPartialFractionConstant +
          (7 / 2 : ℝ) * (sharpLandauMassConstant + 1) *
            sharpLandauMassConstant) * Real.log T ^ 2 := by ring

end GafniTao
