import GafniTao.PintzMajorantBounds

/-!
# A uniform decaying envelope for Pintz's contour error

This is a direct estimate of the literal right and horizontal contour terms.
The cutoff square root is responsible for changing `exp(-lambda)` to
`exp(-lambda/2)`; that loss is kept explicit.
-/

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

noncomputable def pintzContourErrorCoefficient : ℝ :=
  hughesYoungZetaHalfPlaneMajorant ^ 2 *
      (Real.sqrt (8 * Real.pi) / 3) * Real.exp 2 +
    12 * Real.exp 4

theorem pintzContourErrorCoefficient_pos :
    0 < pintzContourErrorCoefficient := by
  unfold pintzContourErrorCoefficient
  have hsecond : 0 < 12 * Real.exp 4 := mul_pos (by norm_num) (Real.exp_pos _)
  have hfirst : 0 ≤ hughesYoungZetaHalfPlaneMajorant ^ 2 *
      (Real.sqrt (8 * Real.pi) / 3) * Real.exp 2 := by positivity
  linarith

theorem sqrt_pintzMobiusCutoff_le
    {lambda : ℝ} (hlambda : 8 ≤ lambda) :
    Real.sqrt (pintzMobiusCutoff lambda) ≤
      2 * Real.exp ((lambda + 3) / 2) := by
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · have hcut := pintzMobiusCutoff_cast_lt_two_exp (by linarith : -3 ≤ lambda)
    have hexp : 0 < Real.exp (lambda + 3) := Real.exp_pos _
    have hsquare : (2 * Real.exp ((lambda + 3) / 2)) ^ 2 =
        4 * Real.exp (lambda + 3) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      norm_num
      ring
    rw [hsquare]
    nlinarith

theorem sqrt_pintzHarmonic_le
    {lambda : ℝ} (hlambda : 8 ≤ lambda) :
    Real.sqrt (harmonic (pintzMobiusCutoff lambda) : ℝ) ≤ lambda + 5 := by
  rw [Real.sqrt_le_iff]
  constructor
  · linarith
  · have hH := pintzMobiusCutoff_harmonic_le
      (lambda := lambda) (by linarith : -3 ≤ lambda)
    have hHnonneg : 0 ≤ (harmonic (pintzMobiusCutoff lambda) : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      positivity
    nlinarith

theorem sqrt_rightGaussianFactor_le
    {lambda : ℝ} (hlambda : 8 ≤ lambda) :
    Real.sqrt (Real.pi / (1 / (8 * lambda))) ≤
      Real.sqrt (8 * Real.pi) * lambda := by
  have hlambdaPos : 0 < lambda := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hrewrite : Real.pi / (1 / (8 * lambda)) = 8 * Real.pi * lambda := by
    field_simp [hlambdaPos.ne']
  rw [hrewrite, Real.sqrt_mul (by positivity : 0 ≤ 8 * Real.pi)]
  have hsqrt : Real.sqrt lambda ≤ lambda := by
    rw [Real.sqrt_le_iff]
    constructor <;> nlinarith
  exact mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _)

theorem pintzUniformRightTailBound_le_errorEnvelope
    {lambda : ℝ} (hlambda : 8 ≤ lambda) :
    pintzUniformRightTailBound lambda ≤
      (hughesYoungZetaHalfPlaneMajorant ^ 2 *
          (Real.sqrt (8 * Real.pi) / 3) * Real.exp 2) *
        (lambda + 5) * Real.exp (-lambda / 2) := by
  have hlambdaPos : 0 < lambda := by linarith
  have hsqrt := sqrt_rightGaussianFactor_le hlambda
  have hexpArg : 9 / lambda ≤ 2 := by
    apply (div_le_iff₀ hlambdaPos).mpr
    nlinarith
  have hexpCombine :
      Real.exp (9 / lambda + 3 * lambda) *
          Real.exp (-(7 / 2 : ℝ) * lambda) =
        Real.exp (9 / lambda) * Real.exp (-lambda / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hexpBound : Real.exp (9 / lambda) ≤ Real.exp 2 :=
    Real.exp_le_exp.mpr hexpArg
  unfold pintzUniformRightTailBound
  calc
    hughesYoungZetaHalfPlaneMajorant ^ 2 *
        ((1 / 3 : ℝ) * Real.exp (9 / lambda + 3 * lambda)) *
        (Real.exp (-(7 / 2 : ℝ) * lambda) *
          Real.sqrt (Real.pi / (1 / (8 * lambda)))) =
      hughesYoungZetaHalfPlaneMajorant ^ 2 * (1 / 3 : ℝ) *
        (Real.exp (9 / lambda + 3 * lambda) *
          Real.exp (-(7 / 2 : ℝ) * lambda)) *
        Real.sqrt (Real.pi / (1 / (8 * lambda))) := by ring
    _ = hughesYoungZetaHalfPlaneMajorant ^ 2 * (1 / 3 : ℝ) *
        (Real.exp (9 / lambda) * Real.exp (-lambda / 2)) *
        Real.sqrt (Real.pi / (1 / (8 * lambda))) := by rw [hexpCombine]
    _ ≤ hughesYoungZetaHalfPlaneMajorant ^ 2 * (1 / 3 : ℝ) *
        (Real.exp 2 * Real.exp (-lambda / 2)) *
        Real.sqrt (Real.pi / (1 / (8 * lambda))) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hexpBound (Real.exp_pos _).le)
          (by positivity)) (Real.sqrt_nonneg _)
    _ ≤ hughesYoungZetaHalfPlaneMajorant ^ 2 * (1 / 3 : ℝ) *
          (Real.exp 2 * Real.exp (-lambda / 2)) *
          (Real.sqrt (8 * Real.pi) * lambda) := by
      exact mul_le_mul_of_nonneg_left hsqrt (by positivity)
    _ = (hughesYoungZetaHalfPlaneMajorant ^ 2 *
          (Real.sqrt (8 * Real.pi) / 3) * Real.exp 2) *
        lambda * Real.exp (-lambda / 2) := by ring
    _ ≤ (hughesYoungZetaHalfPlaneMajorant ^ 2 *
          (Real.sqrt (8 * Real.pi) / 3) * Real.exp 2) *
        (lambda + 5) * Real.exp (-lambda / 2) := by
      have hcoeff : 0 ≤ hughesYoungZetaHalfPlaneMajorant ^ 2 *
          (Real.sqrt (8 * Real.pi) / 3) * Real.exp 2 := by positivity
      have hle : lambda ≤ lambda + 5 := by linarith
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hle hcoeff) (Real.exp_pos _).le

theorem two_mul_pintzHorizontalBound_le_errorEnvelope
    {lambda Z : ℝ} (hlambda : 8 ≤ lambda) (hZ : 0 ≤ Z) :
    2 * pintzEquation46HorizontalBound lambda Z ≤
      (12 * Real.exp 4) * Z * (lambda + 5) *
        Real.exp (-lambda / 2) := by
  have hlambdaPos : 0 < lambda := by linarith
  have hcut := sqrt_pintzMobiusCutoff_le hlambda
  have hH := sqrt_pintzHarmonic_le hlambda
  have hexpArg : 9 / lambda + 3 / 2 ≤ 4 := by
    have : 9 / lambda ≤ 2 := by
      apply (div_le_iff₀ hlambdaPos).mpr
      nlinarith
    linarith
  have hexpCombine :
      Real.exp ((lambda + 3) / 2) *
          Real.exp (9 / lambda - lambda) =
        Real.exp (9 / lambda + 3 / 2) * Real.exp (-lambda / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hexpBound : Real.exp (9 / lambda + 3 / 2) ≤ Real.exp 4 :=
    Real.exp_le_exp.mpr hexpArg
  have hinv : lambda⁻¹ ≤ 1 :=
    (inv_le_one₀ hlambdaPos).mpr (by linarith)
  unfold pintzEquation46HorizontalBound
  calc
    2 * (6 * (Z *
        (Real.sqrt (pintzMobiusCutoff lambda) *
          Real.sqrt (harmonic (pintzMobiusCutoff lambda) : ℝ)) *
        Real.exp (9 / lambda - lambda) / (2 * lambda))) =
      6 * Z * Real.sqrt (pintzMobiusCutoff lambda) *
        Real.sqrt (harmonic (pintzMobiusCutoff lambda) : ℝ) *
        Real.exp (9 / lambda - lambda) / lambda := by ring
    _ ≤ 6 * Z * (2 * Real.exp ((lambda + 3) / 2)) *
        (lambda + 5) * Real.exp (9 / lambda - lambda) / lambda := by
      gcongr
    _ = 12 * Z * (lambda + 5) *
        (Real.exp (9 / lambda + 3 / 2) * Real.exp (-lambda / 2)) /
          lambda := by rw [← hexpCombine]; ring
    _ ≤ 12 * Z * (lambda + 5) *
        (Real.exp 4 * Real.exp (-lambda / 2)) / lambda := by gcongr
    _ ≤ 12 * Z * (lambda + 5) *
        (Real.exp 4 * Real.exp (-lambda / 2)) := by
      rw [div_eq_mul_inv]
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hinv (by positivity :
          0 ≤ 12 * Z * (lambda + 5) *
            (Real.exp 4 * Real.exp (-lambda / 2)))
    _ = (12 * Real.exp 4) * Z * (lambda + 5) *
        Real.exp (-lambda / 2) := by ring

theorem pintzUniformEquation46ErrorBound_le_errorEnvelope
    {lambda Z : ℝ} (hlambda : 8 ≤ lambda) (hZ : 0 ≤ Z) :
    pintzUniformEquation46ErrorBound lambda Z ≤
      pintzContourErrorCoefficient * (1 + Z) * (lambda + 5) *
        Real.exp (-lambda / 2) := by
  have hright := pintzUniformRightTailBound_le_errorEnvelope hlambda
  have hhorizontal := two_mul_pintzHorizontalBound_le_errorEnvelope hlambda hZ
  unfold pintzUniformEquation46ErrorBound pintzContourErrorCoefficient
  have hR : 0 ≤ hughesYoungZetaHalfPlaneMajorant ^ 2 *
      (Real.sqrt (8 * Real.pi) / 3) * Real.exp 2 := by positivity
  have hH : 0 ≤ 12 * Real.exp 4 := by positivity
  have hrest : 0 ≤ (lambda + 5) * Real.exp (-lambda / 2) := by positivity
  let R : ℝ := hughesYoungZetaHalfPlaneMajorant ^ 2 *
    (Real.sqrt (8 * Real.pi) / 3) * Real.exp 2
  let H : ℝ := 12 * Real.exp 4
  have hright' : pintzUniformRightTailBound lambda ≤
      R * ((lambda + 5) * Real.exp (-lambda / 2)) := by
    simpa only [R, mul_assoc] using hright
  have hhorizontal' : 2 * pintzEquation46HorizontalBound lambda Z ≤
      (H * Z) * ((lambda + 5) * Real.exp (-lambda / 2)) := by
    simpa only [H, mul_assoc] using hhorizontal
  have hcoeff : R + H * Z ≤ (R + H) * (1 + Z) := by
    dsimp [R, H]
    have hRZ : 0 ≤
        (hughesYoungZetaHalfPlaneMajorant ^ 2 *
          (Real.sqrt (8 * Real.pi) / 3) * Real.exp 2) * Z :=
      mul_nonneg hR hZ
    nlinarith
  calc
    pintzUniformRightTailBound lambda +
        2 * pintzEquation46HorizontalBound lambda Z ≤
      R * ((lambda + 5) * Real.exp (-lambda / 2)) +
        (H * Z) * ((lambda + 5) * Real.exp (-lambda / 2)) :=
      add_le_add hright' hhorizontal'
    _ = (R + H * Z) * ((lambda + 5) * Real.exp (-lambda / 2)) := by ring
    _ ≤ ((R + H) * (1 + Z)) *
        ((lambda + 5) * Real.exp (-lambda / 2)) :=
      mul_le_mul_of_nonneg_right hcoeff hrest
    _ = (hughesYoungZetaHalfPlaneMajorant ^ 2 *
          (Real.sqrt (8 * Real.pi) / 3) * Real.exp 2 + 12 * Real.exp 4) *
        (1 + Z) * (lambda + 5) * Real.exp (-lambda / 2) := by
      simp only [R, H]
      ring

#print axioms pintzUniformEquation46ErrorBound_le_errorEnvelope

end

end GafniTao
