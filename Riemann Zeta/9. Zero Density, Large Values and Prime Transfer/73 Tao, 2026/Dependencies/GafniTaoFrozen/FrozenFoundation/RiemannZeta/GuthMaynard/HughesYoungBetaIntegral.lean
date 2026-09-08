import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Function.JacobianOneDim

open Complex MeasureTheory Set
open scoped Interval

noncomputable section

namespace RiemannZeta.GuthMaynard

private noncomputable def betaIoiMap (x : ℝ) : ℝ := x / (1 - x)

private theorem betaIoiMap_image : betaIoiMap '' Set.Ioo (0 : ℝ) 1 = Set.Ioi 0 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact div_pos hx.1 (sub_pos.mpr hx.2)
  · intro hy
    let x := y / (1 + y)
    have hy0 : 0 < y := hy
    have hden : 0 < 1 + y := by linarith
    have hx0 : 0 < x := div_pos hy0 hden
    have hx1 : x < 1 := (div_lt_one hden).2 (by linarith)
    refine ⟨x, ⟨hx0, hx1⟩, ?_⟩
    dsimp [betaIoiMap, x]
    field_simp
    ring

private theorem betaIoiMap_deriv (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivWithinAt betaIoiMap ((1 - x)⁻¹ ^ 2) (Set.Ioo (0 : ℝ) 1) x := by
  have hne : 1 - x ≠ 0 := (sub_pos.mpr hx.2).ne'
  have hq := (hasDerivAt_id x).div
    ((hasDerivAt_const x 1).sub (hasDerivAt_id x)) hne
  have heq :
      (1 * (1 - x) - x * (0 - 1)) / (1 - x) ^ 2 =
        (1 - x)⁻¹ ^ 2 := by
    field_simp [hne]
    ring
  change HasDerivWithinAt (fun y : ℝ => y / (1 - y))
    ((1 - x)⁻¹ ^ 2) (Set.Ioo (0 : ℝ) 1) x
  convert hq.hasDerivWithinAt using 1
  simpa only [id_eq, Pi.sub_apply] using heq.symm

private theorem betaIoiMap_inj : Set.InjOn betaIoiMap (Set.Ioo (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have hxne : 1 - x ≠ 0 := (sub_pos.mpr hx.2).ne'
  have hyne : 1 - y ≠ 0 := (sub_pos.mpr hy.2).ne'
  dsimp [betaIoiMap] at hxy
  field_simp [hxne, hyne] at hxy
  linarith

theorem hughesYoung_betaIntegral_Ioi
    (u v : ℂ) :
    (∫ x in Set.Ioi (0 : ℝ),
      (x : ℂ) ^ (u - 1) * (1 + (x : ℂ)) ^ (-(u + v))) =
      Complex.betaIntegral u v := by
  let g : ℝ → ℂ := fun x =>
    (x : ℂ) ^ (u - 1) * (1 + (x : ℂ)) ^ (-(u + v))
  have hchange := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioo betaIoiMap_deriv betaIoiMap_inj g
  rw [betaIoiMap_image] at hchange
  rw [hchange]
  rw [Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num)]
  rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
  intro x hx
  have hx0 : 0 < x := hx.1
  have hx1 : 0 < 1 - x := sub_pos.mpr hx.2
  have hx0C : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  have hx1C : ((1 - x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx1.ne'
  have hone : (1 + (betaIoiMap x : ℂ)) = ((1 - x : ℝ) : ℂ)⁻¹ := by
    have hr : 1 + betaIoiMap x = (1 - x)⁻¹ := by
      dsimp [betaIoiMap]
      field_simp [hx1.ne']
      ring
    exact_mod_cast hr
  have hmap : (betaIoiMap x : ℂ) = (x : ℂ) * ((1 - x : ℝ) : ℂ)⁻¹ := by
    dsimp [betaIoiMap]
    push_cast
    rw [div_eq_mul_inv]
  have hderiv : |(1 - x)⁻¹ ^ 2| = (1 - x)⁻¹ ^ 2 := by
    rw [abs_of_pos]
    positivity
  simp only [g, hderiv]
  rw [hone, hmap]
  rw [Complex.real_smul]
  have hcastInv : (↑x * (↑(1 - x))⁻¹ : ℂ) =
      (x : ℂ) * (((1 - x)⁻¹ : ℝ) : ℂ) := by
    rw [Complex.ofReal_inv]
  rw [hcastInv]
  rw [Complex.mul_cpow_ofReal_nonneg hx0.le (inv_nonneg.mpr hx1.le)]
  push_cast
  have harg : (1 - (x : ℂ)).arg ≠ Real.pi := by
    rw [show (1 - (x : ℂ)) = ((1 - x : ℝ) : ℂ) by push_cast; rfl]
    rw [arg_ofReal_of_nonneg hx1.le]
    exact ne_of_lt Real.pi_pos
  rw [Complex.inv_cpow _ _ harg]
  rw [Complex.inv_cpow _ _ harg]
  rw [inv_pow]
  rw [← Complex.cpow_natCast]
  rw [← Complex.cpow_neg]
  rw [← Complex.cpow_neg]
  rw [← Complex.cpow_neg]
  have hbaseC : (1 - (x : ℂ)) ≠ 0 := by
    simpa only [Complex.ofReal_sub, Complex.ofReal_one] using hx1C
  calc
    (1 - (x : ℂ)) ^ (-(2 : ℂ)) *
          ((x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ (-(u - 1)) *
            (1 - (x : ℂ)) ^ (-(-(u + v)))) =
        (x : ℂ) ^ (u - 1) *
          (((1 - (x : ℂ)) ^ (-(2 : ℂ)) *
              (1 - (x : ℂ)) ^ (-(u - 1))) *
            (1 - (x : ℂ)) ^ (-(-(u + v)))) := by ring
    _ = (x : ℂ) ^ (u - 1) *
        (1 - (x : ℂ)) ^ (-(2 : ℂ) + -(u - 1) + -(-(u + v))) := by
      rw [← Complex.cpow_add _ _ hbaseC, ← Complex.cpow_add _ _ hbaseC]
    _ = (x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ (v - 1) := by
      congr 1
      congr 1
      ring

theorem hughesYoung_betaIntegral_Ioi_eq_gamma
    {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    (∫ x in Set.Ioi (0 : ℝ),
      (x : ℂ) ^ (u - 1) * (1 + (x : ℂ)) ^ (-(u + v))) =
      Complex.Gamma u * Complex.Gamma v / Complex.Gamma (u + v) := by
  rw [hughesYoung_betaIntegral_Ioi u v]
  exact Complex.betaIntegral_eq_Gamma_mul_div u v hu hv

/-- The beta integral which occurs after Hughes--Young's positive/negative
shift substitutions.  The parameters here are forced by the displayed
integrand: its `x` exponent is `u - 1`, while its `(1+x)` exponent is
`-(u+v)`.  In particular, the first Gamma factor contains `gamma` and the
denominator contains `alpha` (the opposite ordering printed in the line
following equation (84) of the source TeX is a typographical transposition).
-/
theorem hughesYoung_equation84_corrected
    {alpha gamma s z : ℂ}
    (hu : 0 < (1 / 2 - gamma - s + z).re)
    (hv : 0 < (alpha + gamma + 2 * s).re) :
    (∫ x in Set.Ioi (0 : ℝ),
      (x : ℂ) ^ (-1 / 2 - gamma - s + z) *
        (1 + (x : ℂ)) ^ (-1 / 2 - alpha - s - z)) =
      Complex.Gamma (1 / 2 - gamma - s + z) *
          Complex.Gamma (alpha + gamma + 2 * s) /
        Complex.Gamma (1 / 2 + alpha + s + z) := by
  have h := hughesYoung_betaIntegral_Ioi_eq_gamma hu hv
  convert h using 1 <;> ring_nf

/-- Real-ordinate form of the corrected equation (84).  Taking `sign = 1`
or `sign = -1` gives the two source integrals.  The convergence hypotheses
are independent of the ordinate because `sign * t * I` is purely imaginary.
-/
theorem hughesYoung_equation84_signed
    {alpha gamma s : ℂ} (sign t : ℝ)
    (hu : 0 < (1 / 2 - gamma - s).re)
    (hv : 0 < (alpha + gamma + 2 * s).re) :
    (∫ x in Set.Ioi (0 : ℝ),
      (x : ℂ) ^
          (-1 / 2 - gamma - s + ((sign * t : ℝ) : ℂ) * I) *
        (1 + (x : ℂ)) ^
          (-1 / 2 - alpha - s - ((sign * t : ℝ) : ℂ) * I)) =
      Complex.Gamma
          (1 / 2 - gamma - s + ((sign * t : ℝ) : ℂ) * I) *
          Complex.Gamma (alpha + gamma + 2 * s) /
        Complex.Gamma
          (1 / 2 + alpha + s + ((sign * t : ℝ) : ℂ) * I) := by
  apply hughesYoung_equation84_corrected
  · simpa [Complex.mul_re] using hu
  · exact hv

/-- The positive-shift dilation used immediately before Hughes--Young
equation (84).  It is stated for arbitrary complex exponents so that the two
logarithmic DFI factors can subsequently be recovered by differentiation in
the exponent parameters. -/
theorem hughesYoung_scaledBetaIntegral
    {A B : ℂ} {r : ℝ} (hr : 0 < r) :
    (∫ y in Set.Ioi (0 : ℝ),
      (y : ℂ) ^ A * ((y + r : ℝ) : ℂ) ^ B) =
      (r : ℂ) ^ (A + B + 1) *
        ∫ x in Set.Ioi (0 : ℝ),
          (x : ℂ) ^ A * (1 + (x : ℂ)) ^ B := by
  let g : ℝ → ℂ := fun y => (y : ℂ) ^ A * ((y + r : ℝ) : ℂ) ^ B
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hs := MeasureTheory.integral_comp_mul_left_Ioi g 0 hr
  rw [mul_zero] at hs
  have hi :
      (∫ x in Set.Ioi (0 : ℝ), g (r * x)) =
        (r : ℂ) ^ (A + B) *
          ∫ x in Set.Ioi (0 : ℝ),
            (x : ℂ) ^ A * (1 + (x : ℂ)) ^ B := by
    calc
      (∫ x in Set.Ioi (0 : ℝ), g (r * x)) =
          ∫ x in Set.Ioi (0 : ℝ),
            (r : ℂ) ^ (A + B) *
              ((x : ℂ) ^ A * (1 + (x : ℂ)) ^ B) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        dsimp only [g]
        have hxr : ((r * x + r : ℝ) : ℂ) =
            (r : ℂ) * (1 + (x : ℂ)) := by
          push_cast
          ring
        rw [show ((r * x : ℝ) : ℂ) =
            (r : ℂ) * (x : ℂ) by push_cast; rfl, hxr]
        rw [Complex.mul_cpow_ofReal_nonneg hr.le hx.le]
        have hone : (1 + (x : ℂ)) = (((1 + x : ℝ) : ℂ)) := by
          push_cast
          rfl
        rw [hone]
        rw [Complex.mul_cpow_ofReal_nonneg hr.le
          (add_nonneg zero_le_one hx.le)]
        calc
          (r : ℂ) ^ A * (x : ℂ) ^ A *
              ((r : ℂ) ^ B * (((1 + x : ℝ) : ℂ)) ^ B) =
              ((r : ℂ) ^ A * (r : ℂ) ^ B) *
                ((x : ℂ) ^ A * (((1 + x : ℝ) : ℂ)) ^ B) := by ring
          _ = _ := by rw [← Complex.cpow_add _ _ hrC]
      _ = _ := MeasureTheory.integral_const_mul _ _
  rw [hi] at hs
  have hcast : (((r⁻¹ : ℝ) : ℂ)) = (r : ℂ)⁻¹ := by
    push_cast
    rfl
  rw [Complex.real_smul, hcast] at hs
  let J : ℂ := ∫ y in Set.Ioi (0 : ℝ),
    (y : ℂ) ^ A * ((y + r : ℝ) : ℂ) ^ B
  let Iβ : ℂ := ∫ x in Set.Ioi (0 : ℝ),
    (x : ℂ) ^ A * (1 + (x : ℂ)) ^ B
  change J = _
  change (r : ℂ) ^ (A + B) * Iβ = (r : ℂ)⁻¹ * J at hs
  calc
    J = (r : ℂ) * ((r : ℂ)⁻¹ * J) := by field_simp
    _ = (r : ℂ) * ((r : ℂ) ^ (A + B) * Iβ) := by rw [← hs]
    _ = (r : ℂ) ^ (A + B + 1) * Iβ := by
      have hp : (r : ℂ) * (r : ℂ) ^ (A + B) =
          (r : ℂ) ^ (A + B + 1) := by
        calc
          (r : ℂ) * (r : ℂ) ^ (A + B) =
              (r : ℂ) ^ (1 : ℂ) * (r : ℂ) ^ (A + B) := by
                congr 1
                exact (Complex.cpow_one _).symm
          _ = (r : ℂ) ^ ((1 : ℂ) + (A + B)) :=
            (Complex.cpow_add _ _ hrC).symm
          _ = (r : ℂ) ^ (A + B + 1) := by
            congr 1
            ring
      rw [← mul_assoc, hp]

/-- Dilation of an `Ioi 0` Bochner integral, with the Jacobian written on
the source side.  This form is convenient for the logarithmic factors in
DFI equation (27). -/
theorem integral_Ioi_eq_mul_integral_dilate
    (g : ℝ → ℂ) {r : ℝ} (hr : 0 < r) :
    (∫ y in Set.Ioi (0 : ℝ), g y) =
      (r : ℂ) * ∫ x in Set.Ioi (0 : ℝ), g (r * x) := by
  have hs := MeasureTheory.integral_comp_mul_left_Ioi g 0 hr
  rw [mul_zero, Complex.real_smul] at hs
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hcast : (((r⁻¹ : ℝ) : ℂ)) = (r : ℂ)⁻¹ := by
    push_cast
    rfl
  rw [hcast] at hs
  calc
    (∫ y in Set.Ioi (0 : ℝ), g y) =
        (r : ℂ) * ((r : ℂ)⁻¹ * ∫ y in Set.Ioi (0 : ℝ), g y) := by
          field_simp
    _ = (r : ℂ) * ∫ x in Set.Ioi (0 : ℝ), g (r * x) := by
          rw [hs]

/-- The exact physical-to-beta dilation with both logarithmic factors kept.
This is the integral identity needed for the two main terms produced by the
DFI Voronoi formula; no absolute values have been taken, so the later signed
Hughes--Young cancellation remains available. -/
theorem hughesYoung_scaledLogBetaIntegral
    {A B C D : ℂ} {r : ℝ} (hr : 0 < r) :
    (∫ y in Set.Ioi (0 : ℝ),
      ((Real.log y : ℂ) + C) *
        ((Real.log (y + r) : ℂ) + D) *
        ((y : ℂ) ^ A * ((y + r : ℝ) : ℂ) ^ B)) =
      (r : ℂ) ^ (A + B + 1) *
        ∫ x in Set.Ioi (0 : ℝ),
          ((Real.log r : ℂ) + (Real.log x : ℂ) + C) *
            ((Real.log r : ℂ) + (Real.log (1 + x) : ℂ) + D) *
            ((x : ℂ) ^ A * (1 + (x : ℂ)) ^ B) := by
  let g : ℝ → ℂ := fun y =>
    ((Real.log y : ℂ) + C) *
      ((Real.log (y + r) : ℂ) + D) *
      ((y : ℂ) ^ A * ((y + r : ℝ) : ℂ) ^ B)
  rw [integral_Ioi_eq_mul_integral_dilate g hr]
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hi :
      (∫ x in Set.Ioi (0 : ℝ), g (r * x)) =
        (r : ℂ) ^ (A + B) *
          ∫ x in Set.Ioi (0 : ℝ),
            ((Real.log r : ℂ) + (Real.log x : ℂ) + C) *
              ((Real.log r : ℂ) + (Real.log (1 + x) : ℂ) + D) *
              ((x : ℂ) ^ A * (1 + (x : ℂ)) ^ B) := by
    calc
      (∫ x in Set.Ioi (0 : ℝ), g (r * x)) =
          ∫ x in Set.Ioi (0 : ℝ),
            (r : ℂ) ^ (A + B) *
              (((Real.log r : ℂ) + (Real.log x : ℂ) + C) *
                ((Real.log r : ℂ) + (Real.log (1 + x) : ℂ) + D) *
                ((x : ℂ) ^ A * (1 + (x : ℂ)) ^ B)) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        have hrx : 0 < r * x := mul_pos hr hx
        have hsum : r * x + r = r * (1 + x) := by ring
        have hsumPos : 0 < 1 + x := add_pos_of_nonneg_of_pos zero_le_one hx
        have hlog1 : Real.log (r * x) = Real.log r + Real.log x :=
          Real.log_mul hr.ne' hx.ne'
        have hlog2 : Real.log (r * x + r) =
            Real.log r + Real.log (1 + x) := by
          rw [hsum, Real.log_mul hr.ne' hsumPos.ne']
        dsimp only [g]
        rw [hlog1, hlog2, hsum]
        rw [show ((r * x : ℝ) : ℂ) =
            (r : ℂ) * (x : ℂ) by push_cast; rfl]
        rw [show ((r * (1 + x) : ℝ) : ℂ) =
            (r : ℂ) * (((1 + x : ℝ) : ℂ)) by push_cast; rfl]
        rw [Complex.mul_cpow_ofReal_nonneg hr.le hx.le]
        rw [Complex.mul_cpow_ofReal_nonneg hr.le hsumPos.le]
        have hone : (1 + (x : ℂ)) = (((1 + x : ℝ) : ℂ)) := by
          push_cast
          rfl
        rw [hone]
        push_cast
        calc
          ((Real.log r : ℂ) + (Real.log x : ℂ) + C) *
                ((Real.log r : ℂ) + (Real.log (1 + x) : ℂ) + D) *
                ((r : ℂ) ^ A * (x : ℂ) ^ A *
                  ((r : ℂ) ^ B * (1 + (x : ℂ)) ^ B)) =
              ((r : ℂ) ^ A * (r : ℂ) ^ B) *
                (((Real.log r : ℂ) + (Real.log x : ℂ) + C) *
                  ((Real.log r : ℂ) + (Real.log (1 + x) : ℂ) + D) *
                  ((x : ℂ) ^ A * (1 + (x : ℂ)) ^ B)) := by ring
          _ = _ := by rw [← Complex.cpow_add _ _ hrC]
      _ = _ := MeasureTheory.integral_const_mul _ _
  rw [hi, ← mul_assoc]
  congr 1
  calc
    (r : ℂ) * (r : ℂ) ^ (A + B) =
        (r : ℂ) ^ (1 : ℂ) * (r : ℂ) ^ (A + B) := by
          congr 1
          exact (Complex.cpow_one _).symm
    _ = (r : ℂ) ^ ((1 : ℂ) + (A + B)) :=
      (Complex.cpow_add _ _ hrC).symm
    _ = (r : ℂ) ^ (A + B + 1) := by
      congr 1
      ring

/-- Equations (83)--(84), including the physical positive-shift scale
`r`.  The exponent of `r` is the exact Jacobian-plus-Mellin exponent and is
independent of the ordinate. -/
theorem hughesYoung_equations83_84_positive
    {alpha gamma s : ℂ} (sign t : ℝ) {r : ℝ} (hr : 0 < r)
    (hu : 0 < (1 / 2 - gamma - s).re)
    (hv : 0 < (alpha + gamma + 2 * s).re) :
    (∫ y in Set.Ioi (0 : ℝ),
      (y : ℂ) ^
          (-1 / 2 - gamma - s + ((sign * t : ℝ) : ℂ) * I) *
        ((y + r : ℝ) : ℂ) ^
          (-1 / 2 - alpha - s - ((sign * t : ℝ) : ℂ) * I)) =
      (r : ℂ) ^ (-alpha - gamma - 2 * s) *
        (Complex.Gamma
            (1 / 2 - gamma - s + ((sign * t : ℝ) : ℂ) * I) *
          Complex.Gamma (alpha + gamma + 2 * s) /
          Complex.Gamma
            (1 / 2 + alpha + s + ((sign * t : ℝ) : ℂ) * I)) := by
  rw [hughesYoung_scaledBetaIntegral hr]
  rw [hughesYoung_equation84_signed sign t hu hv]
  congr 2
  ring

end RiemannZeta.GuthMaynard
