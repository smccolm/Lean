import GafniTao.FordZeroDetectorVerticalLog

/-!
# Physical vertical edges in Ford's detector

This file proves the exact affine change of variables from the rectangle
library's physical `VIntegral'` to Ford's parameter
`y = t + (2η/π)u`.  It then establishes interval integrability of the
actual zeta detector integrand from the stated zero-free edge condition.
-/

open Complex Set MeasureTheory
open RiemannZeta.GuthMaynard

namespace GafniTao

noncomputable section

set_option maxHeartbeats 800000

theorem VIntegral'_eq_scaled_param
    (F : ℂ → ℂ) {x t R scale : ℝ} (hscale : scale ≠ 0) :
    VIntegral' F x (t - R) (t + R) =
      ∫ u in (-R / scale)..(R / scale),
        (1 / (2 * (Real.pi : ℂ) * I)) *
          (I * (scale : ℂ)) *
          F ((x : ℂ) + (t + scale * u : ℝ) * I) := by
  let f : ℝ → ℂ := fun y =>
    (1 / (2 * (Real.pi : ℂ) * I)) * I *
      F ((x : ℂ) + (y : ℝ) * I)
  have hchange := intervalIntegral.integral_comp_mul_add
    (f := f) (a := -R / scale) (b := R / scale) hscale t
  have hlower : scale * (-R / scale) + t = t - R := by
    field_simp [hscale]
    ring
  have hupper : scale * (R / scale) + t = t + R := by
    field_simp [hscale]
    ring
  rw [hlower, hupper] at hchange
  have hscaleC : (scale : ℂ) ≠ 0 := by exact_mod_cast hscale
  calc
    VIntegral' F x (t - R) (t + R) =
        ∫ y in t - R..t + R, f y := by
      unfold VIntegral' VIntegral
      simp only [smul_eq_mul]
      rw [← intervalIntegral.integral_const_mul]
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro y _hy
      dsimp only [f]
      ring
    _ = (scale : ℂ) *
        ∫ u in (-R / scale)..(R / scale), f (scale * u + t) := by
      rw [hchange, Complex.real_smul]
      push_cast
      field_simp [hscaleC]
    _ = ∫ u in (-R / scale)..(R / scale),
        (scale : ℂ) * f (scale * u + t) := by
      symm
      exact intervalIntegral.integral_const_mul
        (scale : ℂ) (fun u : ℝ => f (scale * u + t))
    _ = ∫ u in (-R / scale)..(R / scale),
        (1 / (2 * (Real.pi : ℂ) * I)) *
          (I * (scale : ℂ)) *
          F ((x : ℂ) + (t + scale * u : ℝ) * I) := by
      apply intervalIntegral.integral_congr
      intro u _hu
      dsimp only [f]
      push_cast
      ring

theorem intervalIntegrable_fordDetector_verticalParam
    {eta a b : ℝ} (z₀ : ℂ) (side : ℝ)
    (hkernel : ∀ u : ℝ,
      fordCotKernel eta
        ((side : ℂ) + (2 * eta * u / Real.pi : ℝ) * I) =
      -((Real.pi / (2 * eta) : ℝ) : ℂ) *
        (Real.tanh u : ℂ) * I)
    (h1 : ∀ u ∈ uIcc a b,
      z₀ + (side : ℂ) +
          (2 * eta * u / Real.pi : ℝ) * I ≠ 1)
    (hzeta : ∀ u ∈ uIcc a b,
      riemannZeta (z₀ + (side : ℂ) +
        (2 * eta * u / Real.pi : ℝ) * I) ≠ 0) :
    IntervalIntegrable
      (fun u : ℝ =>
        (1 / (2 * (Real.pi : ℂ) * I)) *
          (I * ((2 * eta / Real.pi : ℝ) : ℂ)) *
          fordCotKernel eta
            ((side : ℂ) + (2 * eta * u / Real.pi : ℝ) * I) *
          fordDetectorZetaLogDeriv
            (z₀ + (side : ℂ) +
              (2 * eta * u / Real.pi : ℝ) * I)) volume a b := by
  have hweight : Continuous (fun u : ℝ =>
      fordCotKernel eta
        ((side : ℂ) + (2 * eta * u / Real.pi : ℝ) * I)) := by
    rw [show (fun u : ℝ => fordCotKernel eta
        ((side : ℂ) + (2 * eta * u / Real.pi : ℝ) * I)) =
      fun u : ℝ => -((Real.pi / (2 * eta) : ℝ) : ℂ) *
        (Real.tanh u : ℂ) * I by
      funext u
      exact hkernel u]
    rw [continuous_iff_continuousAt]
    intro u
    exact (((continuousAt_const.mul
      (hasDerivAt_tanh_sechSq u).continuousAt.ofReal).mul
        continuousAt_const))
  apply ContinuousOn.intervalIntegrable
  intro u hu
  have hLCont : ContinuousAt (fun v : ℝ =>
      fordDetectorZetaLogDeriv
        (z₀ + (side : ℂ) +
          (2 * eta * v / Real.pi : ℝ) * I)) u := by
    have hpath : ContinuousAt (fun v : ℝ =>
        z₀ + (side : ℂ) +
          (2 * eta * v / Real.pi : ℝ) * I) u := by fun_prop
    exact (differentiableAt_fordDetectorZetaLogDeriv
      (h1 u hu) (hzeta u hu)).continuousAt.comp_of_eq hpath rfl
  exact ((((continuousAt_const.mul continuousAt_const).mul
    hweight.continuousAt).mul hLCont).continuousWithinAt)

theorem re_VIntegral'_eq_integral_re_scaled_param
    (F : ℂ → ℂ) {x t R scale : ℝ} (hscale : scale ≠ 0)
    (hint : IntervalIntegrable
      (fun u : ℝ =>
        (1 / (2 * (Real.pi : ℂ) * I)) *
          (I * (scale : ℂ)) *
          F ((x : ℂ) + (t + scale * u : ℝ) * I))
      volume (-R / scale) (R / scale)) :
    (VIntegral' F x (t - R) (t + R)).re =
      ∫ u in (-R / scale)..(R / scale),
        ((1 / (2 * (Real.pi : ℂ) * I)) *
          (I * (scale : ℂ)) *
          F ((x : ℂ) + (t + scale * u : ℝ) * I)).re := by
  rw [VIntegral'_eq_scaled_param F hscale]
  exact (intervalIntegral.intervalIntegral_re hint).symm

/-- Exact finite-height formula for either physical detector edge.  The
zero-free premise is on the actual centered edge and the conclusion starts
from the real part of the rectangle library's `VIntegral'`. -/
theorem re_fordZetaDetector_verticalEdge_eq_logIntegral
    {eta t R : ℝ} (heta : 0 < eta) (side : ℝ)
    (hkernel : ∀ u : ℝ,
      fordCotKernel eta
        ((side : ℂ) + (2 * eta * u / Real.pi : ℝ) * I) =
      -((Real.pi / (2 * eta) : ℝ) : ℂ) *
        (Real.tanh u : ℂ) * I)
    (h1 : ∀ u ∈ uIcc (-R / (2 * eta / Real.pi))
        (R / (2 * eta / Real.pi)),
      fordDetectorCenter t + (side : ℂ) +
          (2 * eta * u / Real.pi : ℝ) * I ≠ 1)
    (hzeta : ∀ u ∈ uIcc (-R / (2 * eta / Real.pi))
        (R / (2 * eta / Real.pi)),
      riemannZeta (fordDetectorCenter t + (side : ℂ) +
        (2 * eta * u / Real.pi : ℝ) * I) ≠ 0) :
    (VIntegral' (fordZetaDetectorIntegrand eta (fordDetectorCenter t))
        (1 + side) (t - R) (t + R)).re =
      (1 / (4 * eta)) *
        ((∫ u in (-R / (2 * eta / Real.pi))..
            (R / (2 * eta / Real.pi)),
          Real.log ‖riemannZeta
            (fordDetectorCenter t + (side : ℂ) +
              (2 * eta * u / Real.pi : ℝ) * I)‖ /
            Real.cosh u ^ 2) -
          (Real.tanh (R / (2 * eta / Real.pi)) *
              Real.log ‖riemannZeta
                (fordDetectorCenter t + (side : ℂ) +
                  (2 * eta * (R / (2 * eta / Real.pi)) /
                    Real.pi : ℝ) * I)‖ -
           Real.tanh (-R / (2 * eta / Real.pi)) *
              Real.log ‖riemannZeta
                (fordDetectorCenter t + (side : ℂ) +
                  (2 * eta * (-R / (2 * eta / Real.pi)) /
                    Real.pi : ℝ) * I)‖)) := by
  let scale : ℝ := 2 * eta / Real.pi
  let lo : ℝ := -R / scale
  let hi : ℝ := R / scale
  have hscale : scale ≠ 0 := by
    dsimp only [scale]
    exact div_ne_zero (mul_ne_zero two_ne_zero heta.ne') Real.pi_ne_zero
  let centered : ℝ → ℂ := fun u =>
    (1 / (2 * (Real.pi : ℂ) * I)) *
      (I * ((2 * eta / Real.pi : ℝ) : ℂ)) *
      fordCotKernel eta
        ((side : ℂ) + (2 * eta * u / Real.pi : ℝ) * I) *
      fordDetectorZetaLogDeriv
        (fordDetectorCenter t + (side : ℂ) +
          (2 * eta * u / Real.pi : ℝ) * I)
  let physical : ℝ → ℂ := fun u =>
    (1 / (2 * (Real.pi : ℂ) * I)) *
      (I * (scale : ℂ)) *
      fordZetaDetectorIntegrand eta (fordDetectorCenter t)
        (((1 + side : ℝ) : ℂ) + (t + scale * u : ℝ) * I)
  have hpc : physical = centered := by
    funext u
    have hs :
        (((1 + side : ℝ) : ℂ) + (t + scale * u : ℝ) * I) =
          fordDetectorCenter t + (side : ℂ) +
            (2 * eta * u / Real.pi : ℝ) * I := by
      dsimp only [scale]
      dsimp only [fordDetectorCenter]
      push_cast
      ring
    have hsub :
        (fordDetectorCenter t + (side : ℂ) +
            (2 * eta * u / Real.pi : ℝ) * I) -
            fordDetectorCenter t =
          (side : ℂ) + (2 * eta * u / Real.pi : ℝ) * I := by ring
    dsimp only [physical, centered, fordZetaDetectorIntegrand]
    rw [hs, hsub]
    dsimp only [scale]
    ring
  have hcenterInt : IntervalIntegrable centered volume lo hi := by
    dsimp only [centered, lo, hi, scale]
    exact intervalIntegrable_fordDetector_verticalParam
      (fordDetectorCenter t) side hkernel h1 hzeta
  have hphysicalInt : IntervalIntegrable physical volume lo hi := by
    rw [hpc]
    exact hcenterInt
  have hV := re_VIntegral'_eq_integral_re_scaled_param
    (fordZetaDetectorIntegrand eta (fordDetectorCenter t))
    (x := 1 + side) (t := t) (R := R) (scale := scale)
    hscale hphysicalInt
  have hAbel := integral_re_fordDetector_verticalParam_eq
    heta (fordDetectorCenter t) side hkernel h1 hzeta
  dsimp only [lo, hi] at hcenterInt hphysicalInt
  dsimp only [scale] at hV ⊢
  rw [hV]
  rw [show (fun u : ℝ =>
      ((1 / (2 * (Real.pi : ℂ) * I)) *
        (I * ((2 * eta / Real.pi : ℝ) : ℂ)) *
        fordZetaDetectorIntegrand eta (fordDetectorCenter t)
          (((1 + side : ℝ) : ℂ) +
            (t + (2 * eta / Real.pi) * u : ℝ) * I)).re) =
      fun u => (centered u).re by
    funext u
    rw [← hpc]]
  simpa only [centered, scale, lo, hi] using hAbel

/-- The actual right edge `Re s = 1+η` is automatically pole-free and
zero-free.  This is Ford's finite-height right-edge logarithmic formula. -/
theorem re_fordZetaDetector_rightEdge_eq_logIntegral
    {eta t R : ℝ} (heta : 0 < eta) :
    (VIntegral' (fordZetaDetectorIntegrand eta (fordDetectorCenter t))
        (1 + eta) (t - R) (t + R)).re =
      (1 / (4 * eta)) *
        ((∫ u in (-R / (2 * eta / Real.pi))..
            (R / (2 * eta / Real.pi)),
          Real.log ‖riemannZeta
            (fordDetectorCenter t + (eta : ℂ) +
              (2 * eta * u / Real.pi : ℝ) * I)‖ /
            Real.cosh u ^ 2) -
          (Real.tanh (R / (2 * eta / Real.pi)) *
              Real.log ‖riemannZeta
                (fordDetectorCenter t + (eta : ℂ) +
                  (2 * eta * (R / (2 * eta / Real.pi)) /
                    Real.pi : ℝ) * I)‖ -
           Real.tanh (-R / (2 * eta / Real.pi)) *
              Real.log ‖riemannZeta
                (fordDetectorCenter t + (eta : ℂ) +
                  (2 * eta * (-R / (2 * eta / Real.pi)) /
                    Real.pi : ℝ) * I)‖)) := by
  apply re_fordZetaDetector_verticalEdge_eq_logIntegral
    heta eta (fordCotKernel_pos_vertical heta)
  · intro u _hu hEq
    have hre := congrArg Complex.re hEq
    simp [fordDetectorCenter] at hre
    linarith
  · intro u _hu
    apply riemannZeta_ne_zero_of_one_le_re
    simp [fordDetectorCenter]
    linarith

/-- Ford's finite-height left-edge formula under the literal zero-free-line
condition.  Later the source's good-`η` construction supplies this premise. -/
theorem re_fordZetaDetector_leftEdge_eq_logIntegral
    {eta t R : ℝ} (heta : 0 < eta)
    (hzeta : ∀ u ∈ uIcc (-R / (2 * eta / Real.pi))
        (R / (2 * eta / Real.pi)),
      riemannZeta (fordDetectorCenter t + (-eta : ℂ) +
        (2 * eta * u / Real.pi : ℝ) * I) ≠ 0) :
    (VIntegral' (fordZetaDetectorIntegrand eta (fordDetectorCenter t))
        (1 - eta) (t - R) (t + R)).re =
      (1 / (4 * eta)) *
        ((∫ u in (-R / (2 * eta / Real.pi))..
            (R / (2 * eta / Real.pi)),
          Real.log ‖riemannZeta
            (fordDetectorCenter t + (-eta : ℂ) +
              (2 * eta * u / Real.pi : ℝ) * I)‖ /
            Real.cosh u ^ 2) -
          (Real.tanh (R / (2 * eta / Real.pi)) *
              Real.log ‖riemannZeta
                (fordDetectorCenter t + (-eta : ℂ) +
                  (2 * eta * (R / (2 * eta / Real.pi)) /
                    Real.pi : ℝ) * I)‖ -
           Real.tanh (-R / (2 * eta / Real.pi)) *
              Real.log ‖riemannZeta
                (fordDetectorCenter t + (-eta : ℂ) +
                  (2 * eta * (-R / (2 * eta / Real.pi)) /
                    Real.pi : ℝ) * I)‖)) := by
  simpa using
    (re_fordZetaDetector_verticalEdge_eq_logIntegral
      (eta := eta) (t := t) (R := R) heta (-eta)
      (fun u => by simpa using fordCotKernel_neg_vertical heta u)
      (fun u _hu hEq => by
        have hre := congrArg Complex.re hEq
        simp [fordDetectorCenter] at hre
        linarith)
      (fun u hu => by simpa using hzeta u hu))

end

end GafniTao
