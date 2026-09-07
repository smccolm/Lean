import GafniTao.FordLogLift

/-!
# Explicit logarithm lifts on Ford's horizontal detector edges

This file specializes the interval lift to the actual zeta logarithmic
derivative and Ford cotangent kernel on a horizontal line.  The hypotheses
say literally that the chosen height meets neither the pole nor a zeta zero.
-/

open Complex Set MeasureTheory
open RiemannZeta.GuthMaynard

namespace GafniTao

noncomputable section

def fordHorizontalPoint (t y x : ℝ) : ℂ :=
  (x : ℂ) + (t + y : ℝ) * I

def fordHorizontalOffset (y x : ℝ) : ℂ :=
  (x - 1 : ℝ) + (y : ℝ) * I

def fordHorizontalZeta (t y : ℝ) (x : ℝ) : ℂ :=
  riemannZeta (fordHorizontalPoint t y x)

def fordHorizontalLogDeriv (t y : ℝ) (x : ℝ) : ℂ :=
  fordDetectorZetaLogDeriv (fordHorizontalPoint t y x)

def fordHorizontalWeight (eta y : ℝ) (x : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ) * I)) *
    fordCotKernel eta (fordHorizontalOffset y x)

def fordHorizontalWeightDeriv (eta y : ℝ) (x : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ) * I)) *
    deriv (fordCotKernel eta) (fordHorizontalOffset y x)

def fordHorizontalZetaLogLift (t y a x : ℝ) : ℂ :=
  canonicalIntervalLogLift (fordHorizontalZeta t y)
    (fordHorizontalLogDeriv t y) a x

/-- The branch normalized to zero at the left endpoint.  Its derivative is
still the actual logarithmic derivative, while its norm can be bounded using
only the horizontal logarithmic-derivative estimate. -/
def fordHorizontalNormalizedLogLift (t y a x : ℝ) : ℂ :=
  intervalLogLift 0 (fordHorizontalLogDeriv t y) a x

theorem hasDerivAt_fordHorizontalPoint (t y x : ℝ) :
    HasDerivAt (fordHorizontalPoint t y) 1 x := by
  unfold fordHorizontalPoint
  convert Complex.ofRealCLM.hasDerivAt.const_add
    (((t + y : ℝ) : ℂ) * I) using 1
  all_goals simp [add_comm]

theorem hasDerivAt_fordHorizontalOffset (y x : ℝ) :
    HasDerivAt (fordHorizontalOffset y) 1 x := by
  unfold fordHorizontalOffset
  convert (Complex.ofRealCLM.hasDerivAt.sub_const 1).add_const
    (((y : ℝ) : ℂ) * I) using 1
  all_goals simp

theorem ford_horizontal_scaled_sin_ne_zero
    {eta y x : ℝ} (heta : 0 < eta) (hy : y ≠ 0) :
    Complex.sin
      ((((Real.pi / (2 * eta) : ℝ) : ℂ) *
        fordHorizontalOffset y x)) ≠ 0 := by
  let c : ℝ := Real.pi / (2 * eta)
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  have hscale :
      ((c : ℂ) * fordHorizontalOffset y x) =
        ((c * (x - 1) : ℝ) : ℂ) + ((c * y : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [fordHorizontalOffset]
  have hcy : c * y ≠ 0 := mul_ne_zero hc.ne' hy
  have hsinh : Real.sinh (c * y) ≠ 0 := by
    rw [Real.sinh_ne_zero]
    exact hcy
  apply norm_ne_zero_iff.mp
  rw [show (Real.pi / (2 * eta) : ℝ) = c by rfl, hscale]
  have hsquare := norm_sin_add_mul_I_sq (c * (x - 1)) (c * y)
  intro hnorm
  have : ‖Complex.sin
      (((c * (x - 1) : ℝ) : ℂ) + ((c * y : ℝ) : ℂ) * I)‖ ^ 2 = 0 := by
    rw [hnorm]
    norm_num
  rw [hsquare] at this
  nlinarith [sq_pos_of_ne_zero hsinh]

theorem continuous_fordHorizontalLogDeriv
    {t y : ℝ}
    (h1 : ∀ x : ℝ, fordHorizontalPoint t y x ≠ 1)
    (hzeta : ∀ x : ℝ,
      riemannZeta (fordHorizontalPoint t y x) ≠ 0) :
    Continuous (fordHorizontalLogDeriv t y) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact (differentiableAt_fordDetectorZetaLogDeriv
    (h1 x) (hzeta x)).continuousAt.comp_of_eq
      (hasDerivAt_fordHorizontalPoint t y x).continuousAt rfl

theorem hasDerivAt_fordHorizontalZeta
    {t y x : ℝ}
    (h1 : fordHorizontalPoint t y x ≠ 1)
    (hzeta : riemannZeta (fordHorizontalPoint t y x) ≠ 0) :
    HasDerivAt (fordHorizontalZeta t y)
      (fordHorizontalZeta t y x * fordHorizontalLogDeriv t y x) x := by
  have hz := (differentiableAt_riemannZeta h1).hasDerivAt.comp x
    (hasDerivAt_fordHorizontalPoint t y x)
  have hlog := fordDetectorZetaLogDeriv_eq h1 hzeta
  unfold fordHorizontalZeta fordHorizontalLogDeriv
  rw [hlog]
  convert hz using 1
  unfold logDeriv
  rw [mul_comm]
  simp only [Pi.div_apply]
  rw [div_mul_cancel₀ _ hzeta, mul_one]

theorem hasDerivAt_fordHorizontalWeight
    {eta y x : ℝ} (heta : 0 < eta) (hy : y ≠ 0) :
    HasDerivAt (fordHorizontalWeight eta y)
      (fordHorizontalWeightDeriv eta y x) x := by
  have hsin := ford_horizontal_scaled_sin_ne_zero heta hy (x := x)
  have hk := (hasDerivAt_fordCotKernel hsin).comp x
    (hasDerivAt_fordHorizontalOffset y x)
  unfold fordHorizontalWeight fordHorizontalWeightDeriv
  convert hk.const_mul (1 / (2 * (Real.pi : ℂ) * I)) using 1
  rw [(hasDerivAt_fordCotKernel hsin).deriv]
  ring

theorem continuous_fordHorizontalWeightDeriv
    {eta y : ℝ} (heta : 0 < eta) (hy : y ≠ 0) :
    Continuous (fordHorizontalWeightDeriv eta y) := by
  have hfun : fordHorizontalWeightDeriv eta y = fun x : ℝ =>
      (1 / (2 * (Real.pi : ℂ) * I)) *
        (-(((Real.pi / (2 * eta) : ℝ) : ℂ) ^ 2) /
          Complex.sin
            ((((Real.pi / (2 * eta) : ℝ) : ℂ) *
              fordHorizontalOffset y x)) ^ 2) := by
    funext x
    unfold fordHorizontalWeightDeriv
    rw [(hasDerivAt_fordCotKernel
      (ford_horizontal_scaled_sin_ne_zero heta hy (x := x))).deriv]
  rw [hfun, continuous_iff_continuousAt]
  intro x
  have hsinCont : ContinuousAt (fun u : ℝ =>
      Complex.sin
        ((((Real.pi / (2 * eta) : ℝ) : ℂ) *
          fordHorizontalOffset y u))) x := by
    unfold fordHorizontalOffset
    fun_prop
  exact continuousAt_const.mul
    (continuousAt_const.div (hsinCont.pow 2)
      (pow_ne_zero 2 (ford_horizontal_scaled_sin_ne_zero heta hy)))

theorem exp_fordHorizontalZetaLogLift_eq
    {t y a x : ℝ}
    (h1 : ∀ u : ℝ, fordHorizontalPoint t y u ≠ 1)
    (hzeta : ∀ u : ℝ,
      riemannZeta (fordHorizontalPoint t y u) ≠ 0) :
    Complex.exp (fordHorizontalZetaLogLift t y a x) =
      riemannZeta (fordHorizontalPoint t y x) := by
  exact exp_canonicalIntervalLogLift_eq a x
    (continuous_fordHorizontalLogDeriv h1 hzeta)
    (fun u => hasDerivAt_fordHorizontalZeta (h1 u) (hzeta u))
    (hzeta a)

theorem re_fordHorizontalZetaLogLift_eq_log_norm
    {t y a x : ℝ}
    (h1 : ∀ u : ℝ, fordHorizontalPoint t y u ≠ 1)
    (hzeta : ∀ u : ℝ,
      riemannZeta (fordHorizontalPoint t y u) ≠ 0) :
    (fordHorizontalZetaLogLift t y a x).re =
      Real.log ‖riemannZeta (fordHorizontalPoint t y x)‖ := by
  exact re_canonicalIntervalLogLift_eq_log_norm a x
    (continuous_fordHorizontalLogDeriv h1 hzeta)
    (fun u => hasDerivAt_fordHorizontalZeta (h1 u) (hzeta u))
    (hzeta a)

theorem fordHorizontalNormalizedLogLift_eq_sub
    (t y a x : ℝ) :
    fordHorizontalNormalizedLogLift t y a x =
      fordHorizontalZetaLogLift t y a x -
        Complex.log (fordHorizontalZeta t y a) := by
  unfold fordHorizontalNormalizedLogLift fordHorizontalZetaLogLift
  unfold canonicalIntervalLogLift intervalLogLift
  ring

theorem re_fordHorizontalNormalizedLogLift_eq_log_norm_sub
    {t y a x : ℝ}
    (h1 : ∀ u : ℝ, fordHorizontalPoint t y u ≠ 1)
    (hzeta : ∀ u : ℝ,
      riemannZeta (fordHorizontalPoint t y u) ≠ 0) :
    (fordHorizontalNormalizedLogLift t y a x).re =
      Real.log ‖riemannZeta (fordHorizontalPoint t y x)‖ -
        Real.log ‖riemannZeta (fordHorizontalPoint t y a)‖ := by
  rw [fordHorizontalNormalizedLogLift_eq_sub, Complex.sub_re,
    re_fordHorizontalZetaLogLift_eq_log_norm h1 hzeta,
    Complex.log_re]
  rfl

/-- Exact integration by parts for Ford's normalized horizontal detector
edge.  The boundary term is kept for cancellation with the vertical edges. -/
theorem integral_fordHorizontal_detector_eq_boundary_sub
    {eta t y a b : ℝ} (heta : 0 < eta) (hy : y ≠ 0)
    (h1 : ∀ x : ℝ, fordHorizontalPoint t y x ≠ 1)
    (hzeta : ∀ x : ℝ,
      riemannZeta (fordHorizontalPoint t y x) ≠ 0) :
    (∫ x in a..b,
      fordHorizontalWeight eta y x * fordHorizontalLogDeriv t y x) =
      fordHorizontalWeight eta y b *
          fordHorizontalZetaLogLift t y a b -
        fordHorizontalWeight eta y a *
          Complex.log (fordHorizontalZeta t y a) -
        ∫ x in a..b,
          fordHorizontalWeightDeriv eta y x *
            fordHorizontalZetaLogLift t y a x := by
  exact integral_mul_logDerivative_eq_boundary_sub_canonicalLogLift
    (f := fordHorizontalZeta t y) a b
    (fun x => hasDerivAt_fordHorizontalWeight heta hy)
    (continuous_fordHorizontalWeightDeriv heta hy)
    (continuous_fordHorizontalLogDeriv h1 hzeta)

theorem integral_fordHorizontal_detector_eq_normalized_boundary_sub
    {eta t y a b : ℝ} (heta : 0 < eta) (hy : y ≠ 0)
    (h1 : ∀ x : ℝ, fordHorizontalPoint t y x ≠ 1)
    (hzeta : ∀ x : ℝ,
      riemannZeta (fordHorizontalPoint t y x) ≠ 0) :
    (∫ x in a..b,
      fordHorizontalWeight eta y x * fordHorizontalLogDeriv t y x) =
      fordHorizontalWeight eta y b *
          fordHorizontalNormalizedLogLift t y a b -
        ∫ x in a..b,
          fordHorizontalWeightDeriv eta y x *
            fordHorizontalNormalizedLogLift t y a x := by
  have hip := integral_mul_logDerivative_eq_boundary_sub_logLift
    (h := fordHorizontalWeight eta y)
    (h' := fordHorizontalWeightDeriv eta y)
    (L := fordHorizontalLogDeriv t y)
    0 a b
    (fun x => hasDerivAt_fordHorizontalWeight heta hy)
    (continuous_fordHorizontalWeightDeriv heta hy)
    (continuous_fordHorizontalLogDeriv h1 hzeta)
  simpa [fordHorizontalNormalizedLogLift] using hip

theorem HIntegral'_fordZetaDetector_eq_horizontalIntegral
    (eta t y a b : ℝ) :
    HIntegral' (fordZetaDetectorIntegrand eta (fordDetectorCenter t))
        a b (t + y) =
      ∫ x in a..b,
        fordHorizontalWeight eta y x *
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
          fordDetectorCenter t = fordHorizontalOffset y x := by
    unfold fordDetectorCenter fordHorizontalOffset
    push_cast
    ring
  unfold fordHorizontalWeight fordHorizontalLogDeriv
  unfold fordZetaDetectorIntegrand
  dsimp only
  rw [hoff, hp]
  ring

/-- Actual normalized `HIntegral'` form of the horizontal integration by
parts identity. -/
theorem HIntegral'_fordZetaDetector_eq_boundary_sub
    {eta t y a b : ℝ} (heta : 0 < eta) (hy : y ≠ 0)
    (h1 : ∀ x : ℝ, fordHorizontalPoint t y x ≠ 1)
    (hzeta : ∀ x : ℝ,
      riemannZeta (fordHorizontalPoint t y x) ≠ 0) :
    HIntegral' (fordZetaDetectorIntegrand eta (fordDetectorCenter t))
        a b (t + y) =
      fordHorizontalWeight eta y b *
          fordHorizontalNormalizedLogLift t y a b -
        ∫ x in a..b,
          fordHorizontalWeightDeriv eta y x *
            fordHorizontalNormalizedLogLift t y a x := by
  rw [HIntegral'_fordZetaDetector_eq_horizontalIntegral]
  exact integral_fordHorizontal_detector_eq_normalized_boundary_sub
    heta hy h1 hzeta

theorem fordHorizontalWeight_rightEndpoint
    {eta y : ℝ} (heta : 0 < eta) :
    fordHorizontalWeight eta y (1 + eta) =
      ((-Real.tanh (Real.pi * y / (2 * eta)) /
        (4 * eta) : ℝ) : ℂ) := by
  let u : ℝ := Real.pi * y / (2 * eta)
  have hyScale : 2 * eta * u / Real.pi = y := by
    dsimp only [u]
    field_simp [heta.ne', Real.pi_ne_zero]
  have hoff : fordHorizontalOffset y (1 + eta) =
      (eta : ℂ) + (2 * eta * u / Real.pi : ℝ) * I := by
    unfold fordHorizontalOffset
    rw [hyScale]
    push_cast
    ring
  unfold fordHorizontalWeight
  rw [hoff, fordCotKernel_pos_vertical heta]
  dsimp only [u]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hetaC : (eta : ℂ) ≠ 0 := by exact_mod_cast heta.ne'
  push_cast
  field_simp [hpi, hetaC]
  ring

theorem fordHorizontalWeight_leftEndpoint
    {eta y : ℝ} (heta : 0 < eta) :
    fordHorizontalWeight eta y (1 - eta) =
      ((-Real.tanh (Real.pi * y / (2 * eta)) /
        (4 * eta) : ℝ) : ℂ) := by
  let u : ℝ := Real.pi * y / (2 * eta)
  have hyScale : 2 * eta * u / Real.pi = y := by
    dsimp only [u]
    field_simp [heta.ne', Real.pi_ne_zero]
  have hoff : fordHorizontalOffset y (1 - eta) =
      (-eta : ℂ) + (2 * eta * u / Real.pi : ℝ) * I := by
    unfold fordHorizontalOffset
    rw [hyScale]
    push_cast
    ring
  unfold fordHorizontalWeight
  rw [hoff, fordCotKernel_neg_vertical heta]
  dsimp only [u]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hetaC : (eta : ℂ) ≠ 0 := by exact_mod_cast heta.ne'
  push_cast
  field_simp [hpi, hetaC]
  ring

/-- Real part of the complete horizontal endpoint contribution.  It is the
exact negative of the corresponding top/bottom difference of vertical Abel
boundary terms. -/
theorem re_fordHorizontal_boundary_eq
    {eta t y : ℝ} (heta : 0 < eta)
    (h1 : ∀ x : ℝ, fordHorizontalPoint t y x ≠ 1)
    (hzeta : ∀ x : ℝ,
      riemannZeta (fordHorizontalPoint t y x) ≠ 0) :
    (fordHorizontalWeight eta y (1 + eta) *
          fordHorizontalNormalizedLogLift t y (1 - eta) (1 + eta)).re =
      (-Real.tanh (Real.pi * y / (2 * eta)) / (4 * eta)) *
        (Real.log ‖riemannZeta
            (fordHorizontalPoint t y (1 + eta))‖ -
          Real.log ‖riemannZeta
            (fordHorizontalPoint t y (1 - eta))‖) := by
  rw [fordHorizontalWeight_rightEndpoint heta,
    Complex.mul_re,
    re_fordHorizontalNormalizedLogLift_eq_log_norm_sub h1 hzeta]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

end

end GafniTao
