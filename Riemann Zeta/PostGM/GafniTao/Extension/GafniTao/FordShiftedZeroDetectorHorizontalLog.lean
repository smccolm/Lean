import GafniTao.FordShiftedZeroDetectorVerticalEdges
import GafniTao.FordZeroDetectorHorizontalLog

/-!
# Horizontal Abel identity for a shifted Ford detector
-/

open Complex Set MeasureTheory
open RiemannZeta.GuthMaynard

namespace GafniTao

noncomputable section

def fordShiftedHorizontalOffset (sigma y x : ℝ) : ℂ :=
  ((x - sigma : ℝ) : ℂ) + (y : ℂ) * I

def fordShiftedHorizontalWeight
    (sigma eta y x : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ) * I)) *
    fordCotKernel eta (fordShiftedHorizontalOffset sigma y x)

def fordShiftedHorizontalWeightDeriv
    (sigma eta y x : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ) * I)) *
    deriv (fordCotKernel eta) (fordShiftedHorizontalOffset sigma y x)

def fordShiftedHorizontalRemainder
    (sigma eta t y : ℝ) : ℂ :=
  ∫ x in (sigma - eta)..(sigma + eta),
    fordShiftedHorizontalWeightDeriv sigma eta y x *
      fordHorizontalNormalizedLogLift t y (sigma - eta) x

theorem hasDerivAt_fordShiftedHorizontalOffset
    (sigma y x : ℝ) :
    HasDerivAt (fordShiftedHorizontalOffset sigma y) 1 x := by
  unfold fordShiftedHorizontalOffset
  have hsub : HasDerivAt
      (fun u : ℝ => (u : ℂ) - (sigma : ℂ)) 1 x :=
    Complex.ofRealCLM.hasDerivAt.sub_const (sigma : ℂ)
  convert hsub.add_const (((y : ℝ) : ℂ) * I) using 1
  all_goals simp

theorem ford_shifted_horizontal_scaled_sin_ne_zero
    {sigma eta y x : ℝ} (heta : 0 < eta) (hy : y ≠ 0) :
    Complex.sin
      ((((Real.pi / (2 * eta) : ℝ) : ℂ) *
        fordShiftedHorizontalOffset sigma y x)) ≠ 0 := by
  let c : ℝ := Real.pi / (2 * eta)
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  have hscale :
      ((c : ℂ) * fordShiftedHorizontalOffset sigma y x) =
        ((c * (x - sigma) : ℝ) : ℂ) +
          ((c * y : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [fordShiftedHorizontalOffset]
  have hcy : c * y ≠ 0 := mul_ne_zero hc.ne' hy
  have hsinh : Real.sinh (c * y) ≠ 0 := by
    rw [Real.sinh_ne_zero]
    exact hcy
  apply norm_ne_zero_iff.mp
  rw [show (Real.pi / (2 * eta) : ℝ) = c by rfl, hscale]
  have hsquare := norm_sin_add_mul_I_sq (c * (x - sigma)) (c * y)
  intro hnorm
  have hzero :
      ‖Complex.sin
        (((c * (x - sigma) : ℝ) : ℂ) +
          ((c * y : ℝ) : ℂ) * I)‖ ^ 2 = 0 := by
    rw [hnorm]
    norm_num
  rw [hsquare] at hzero
  nlinarith [sq_pos_of_ne_zero hsinh]

theorem hasDerivAt_fordShiftedHorizontalWeight
    {sigma eta y x : ℝ} (heta : 0 < eta) (hy : y ≠ 0) :
    HasDerivAt (fordShiftedHorizontalWeight sigma eta y)
      (fordShiftedHorizontalWeightDeriv sigma eta y x) x := by
  have hsin := ford_shifted_horizontal_scaled_sin_ne_zero
    (sigma := sigma) heta hy (x := x)
  have hk := (hasDerivAt_fordCotKernel hsin).comp x
    (hasDerivAt_fordShiftedHorizontalOffset sigma y x)
  unfold fordShiftedHorizontalWeight fordShiftedHorizontalWeightDeriv
  convert hk.const_mul (1 / (2 * (Real.pi : ℂ) * I)) using 1
  rw [(hasDerivAt_fordCotKernel hsin).deriv]
  ring

theorem continuous_fordShiftedHorizontalWeightDeriv
    {sigma eta y : ℝ} (heta : 0 < eta) (hy : y ≠ 0) :
    Continuous (fordShiftedHorizontalWeightDeriv sigma eta y) := by
  have hfun : fordShiftedHorizontalWeightDeriv sigma eta y =
      fun x : ℝ =>
        (1 / (2 * (Real.pi : ℂ) * I)) *
          (-(((Real.pi / (2 * eta) : ℝ) : ℂ) ^ 2) /
            Complex.sin
              ((((Real.pi / (2 * eta) : ℝ) : ℂ) *
                fordShiftedHorizontalOffset sigma y x)) ^ 2) := by
    funext x
    unfold fordShiftedHorizontalWeightDeriv
    rw [(hasDerivAt_fordCotKernel
      (ford_shifted_horizontal_scaled_sin_ne_zero
        (sigma := sigma) heta hy (x := x))).deriv]
  rw [hfun, continuous_iff_continuousAt]
  intro x
  have hsinCont : ContinuousAt (fun u : ℝ =>
      Complex.sin
        ((((Real.pi / (2 * eta) : ℝ) : ℂ) *
          fordShiftedHorizontalOffset sigma y u))) x := by
    unfold fordShiftedHorizontalOffset
    fun_prop
  exact continuousAt_const.mul
    (continuousAt_const.div (hsinCont.pow 2)
      (pow_ne_zero 2
        (ford_shifted_horizontal_scaled_sin_ne_zero heta hy)))

theorem integral_fordShiftedHorizontal_detector_eq_normalized_boundary_sub
    {sigma eta t y a b : ℝ} (heta : 0 < eta) (hy : y ≠ 0)
    (h1 : ∀ x : ℝ, fordHorizontalPoint t y x ≠ 1)
    (hzeta : ∀ x : ℝ,
      riemannZeta (fordHorizontalPoint t y x) ≠ 0) :
    (∫ x in a..b,
      fordShiftedHorizontalWeight sigma eta y x *
        fordHorizontalLogDeriv t y x) =
      fordShiftedHorizontalWeight sigma eta y b *
          fordHorizontalNormalizedLogLift t y a b -
        ∫ x in a..b,
          fordShiftedHorizontalWeightDeriv sigma eta y x *
            fordHorizontalNormalizedLogLift t y a x := by
  have hip := integral_mul_logDerivative_eq_boundary_sub_logLift
    (h := fordShiftedHorizontalWeight sigma eta y)
    (h' := fordShiftedHorizontalWeightDeriv sigma eta y)
    (L := fordHorizontalLogDeriv t y)
    0 a b
    (fun x => hasDerivAt_fordShiftedHorizontalWeight heta hy)
    (continuous_fordShiftedHorizontalWeightDeriv heta hy)
    (continuous_fordHorizontalLogDeriv h1 hzeta)
  simpa [fordHorizontalNormalizedLogLift] using hip

theorem HIntegral'_fordZetaShiftedDetector_eq_horizontalIntegral
    (sigma eta t y a b : ℝ) :
    HIntegral'
      (fordZetaDetectorIntegrand eta
        (fordShiftedDetectorCenter sigma t))
      a b (t + y) =
      ∫ x in a..b,
        fordShiftedHorizontalWeight sigma eta y x *
          fordHorizontalLogDeriv t y x := by
  rw [HIntegral', HIntegral]
  simp only [smul_eq_mul]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _hx
  have hp :
      ((x : ℂ) + ((t + y : ℝ) : ℂ) * I) =
        fordHorizontalPoint t y x := by rfl
  have hoff :
      ((x : ℂ) + ((t + y : ℝ) : ℂ) * I) -
          fordShiftedDetectorCenter sigma t =
        fordShiftedHorizontalOffset sigma y x := by
    unfold fordShiftedDetectorCenter fordShiftedHorizontalOffset
    push_cast
    ring
  unfold fordShiftedHorizontalWeight fordHorizontalLogDeriv
  unfold fordZetaDetectorIntegrand
  dsimp only
  rw [hoff, hp]
  ring

theorem HIntegral'_fordZetaShiftedDetector_eq_boundary_sub
    {sigma eta t y a b : ℝ} (heta : 0 < eta) (hy : y ≠ 0)
    (h1 : ∀ x : ℝ, fordHorizontalPoint t y x ≠ 1)
    (hzeta : ∀ x : ℝ,
      riemannZeta (fordHorizontalPoint t y x) ≠ 0) :
    HIntegral'
      (fordZetaDetectorIntegrand eta
        (fordShiftedDetectorCenter sigma t))
      a b (t + y) =
      fordShiftedHorizontalWeight sigma eta y b *
          fordHorizontalNormalizedLogLift t y a b -
        ∫ x in a..b,
          fordShiftedHorizontalWeightDeriv sigma eta y x *
            fordHorizontalNormalizedLogLift t y a x := by
  rw [HIntegral'_fordZetaShiftedDetector_eq_horizontalIntegral]
  exact integral_fordShiftedHorizontal_detector_eq_normalized_boundary_sub
    heta hy h1 hzeta

theorem fordShiftedHorizontalWeight_rightEndpoint
    {sigma eta y : ℝ} (heta : 0 < eta) :
    fordShiftedHorizontalWeight sigma eta y (sigma + eta) =
      ((-Real.tanh (Real.pi * y / (2 * eta)) /
        (4 * eta) : ℝ) : ℂ) := by
  let u : ℝ := Real.pi * y / (2 * eta)
  have hyScale : 2 * eta * u / Real.pi = y := by
    dsimp only [u]
    field_simp [heta.ne', Real.pi_ne_zero]
  have hoff :
      fordShiftedHorizontalOffset sigma y (sigma + eta) =
        (eta : ℂ) + (2 * eta * u / Real.pi : ℝ) * I := by
    unfold fordShiftedHorizontalOffset
    rw [hyScale]
    push_cast
    ring
  unfold fordShiftedHorizontalWeight
  rw [hoff, fordCotKernel_pos_vertical heta]
  dsimp only [u]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hetaC : (eta : ℂ) ≠ 0 := by exact_mod_cast heta.ne'
  push_cast
  field_simp [hpi, hetaC]
  ring

theorem fordShiftedHorizontalWeight_leftEndpoint
    {sigma eta y : ℝ} (heta : 0 < eta) :
    fordShiftedHorizontalWeight sigma eta y (sigma - eta) =
      ((-Real.tanh (Real.pi * y / (2 * eta)) /
        (4 * eta) : ℝ) : ℂ) := by
  let u : ℝ := Real.pi * y / (2 * eta)
  have hyScale : 2 * eta * u / Real.pi = y := by
    dsimp only [u]
    field_simp [heta.ne', Real.pi_ne_zero]
  have hoff :
      fordShiftedHorizontalOffset sigma y (sigma - eta) =
        (-eta : ℂ) + (2 * eta * u / Real.pi : ℝ) * I := by
    unfold fordShiftedHorizontalOffset
    rw [hyScale]
    push_cast
    ring
  unfold fordShiftedHorizontalWeight
  rw [hoff, fordCotKernel_neg_vertical heta]
  dsimp only [u]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hetaC : (eta : ℂ) ≠ 0 := by exact_mod_cast heta.ne'
  push_cast
  field_simp [hpi, hetaC]
  ring

theorem re_fordShiftedHorizontal_boundary_eq
    {sigma eta t y : ℝ} (heta : 0 < eta)
    (h1 : ∀ x : ℝ, fordHorizontalPoint t y x ≠ 1)
    (hzeta : ∀ x : ℝ,
      riemannZeta (fordHorizontalPoint t y x) ≠ 0) :
    (fordShiftedHorizontalWeight sigma eta y (sigma + eta) *
      fordHorizontalNormalizedLogLift t y (sigma - eta)
        (sigma + eta)).re =
      (-Real.tanh (Real.pi * y / (2 * eta)) / (4 * eta)) *
        (Real.log ‖riemannZeta
            (fordHorizontalPoint t y (sigma + eta))‖ -
          Real.log ‖riemannZeta
            (fordHorizontalPoint t y (sigma - eta))‖) := by
  rw [fordShiftedHorizontalWeight_rightEndpoint heta,
    Complex.mul_re,
    re_fordHorizontalNormalizedLogLift_eq_log_norm_sub h1 hzeta]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

end

end GafniTao
