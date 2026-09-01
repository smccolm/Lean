import GafniTao.FordShiftedLeftFullBound
import GafniTao.FordZeroDetectorVerticalLog

/-!
# Integrability of the selected shifted left edge

A selected Ford left boundary avoids both the pole and the zeros of zeta.
Consequently the logarithmic integrand is continuous on the entire compact
scaled edge, and hence on every subinterval used in the high/low split.
-/

open Complex Set MeasureTheory

namespace GafniTao

noncomputable section

theorem intervalIntegrable_fordShiftedLeftCoordinateIntegrand
    {eta sigma t a b : ℝ}
    (hleftOne : sigma - eta ≠ 1)
    (hzeta : ∀ u ∈ uIcc a b,
      riemannZeta
        (fordShiftedDetectorCenter sigma t + (-eta : ℂ) +
          (2 * eta * u / Real.pi : ℝ) * I) ≠ 0) :
    IntervalIntegrable
      (fordShiftedLeftCoordinateIntegrand eta sigma t)
      volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro u hu
  have hpoint :
      (((sigma - eta : ℝ) : ℂ) + I * (t : ℝ)) +
          (u : ℂ) * (((2 * eta / Real.pi : ℝ) : ℂ) * I) =
        fordShiftedDetectorCenter sigma t + (-eta : ℂ) +
          (2 * eta * u / Real.pi : ℝ) * I := by
    simp only [fordShiftedDetectorCenter]
    push_cast
    ring
  have hpathOne :
      (((sigma - eta : ℝ) : ℂ) + I * (t : ℝ)) +
          (u : ℂ) * (((2 * eta / Real.pi : ℝ) : ℂ) * I) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    exact hleftOne hre
  have hpathZeta :
      riemannZeta
        ((((sigma - eta : ℝ) : ℂ) + I * (t : ℝ)) +
          (u : ℂ) * (((2 * eta / Real.pi : ℝ) : ℂ) * I)) ≠ 0 := by
    rw [hpoint]
    exact hzeta u hu
  have hlog := hasDerivAt_log_norm_riemannZeta_affine
    (z := (((sigma - eta : ℝ) : ℂ) + I * (t : ℝ)))
    (d := (((2 * eta / Real.pi : ℝ) : ℂ) * I))
    (x := u) hpathOne hpathZeta
  have hlogCoordinate : ContinuousAt
      (fun v : ℝ => Real.log ‖riemannZeta
        (((sigma - eta : ℝ) : ℂ) +
          I * (t + (2 * eta / Real.pi) * v : ℝ))‖) u := by
    convert hlog.continuousAt using 1
    funext v
    congr 3
    push_cast
    ring
  unfold fordShiftedLeftCoordinateIntegrand
  exact hlogCoordinate.div
    ((Real.continuous_cosh.pow 2).continuousAt)
    (pow_ne_zero 2 (Real.cosh_pos u).ne') |>.continuousWithinAt

theorem intervalIntegrable_fordShiftedLeftCoordinateIntegrand_mono
    {eta sigma t a b c d : ℝ}
    (hint : IntervalIntegrable
      (fordShiftedLeftCoordinateIntegrand eta sigma t) volume a b)
    (hsub : uIcc c d ⊆ uIcc a b) :
    IntervalIntegrable
      (fordShiftedLeftCoordinateIntegrand eta sigma t) volume c d :=
  hint.mono_set hsub

#print axioms intervalIntegrable_fordShiftedLeftCoordinateIntegrand
#print axioms intervalIntegrable_fordShiftedLeftCoordinateIntegrand_mono

end

end GafniTao
