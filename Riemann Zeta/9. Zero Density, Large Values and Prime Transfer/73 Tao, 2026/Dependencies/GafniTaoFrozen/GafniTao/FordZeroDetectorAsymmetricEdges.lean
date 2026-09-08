import GafniTao.FordZeroDetectorAsymmetricRectangle
import GafniTao.FordZeroDetectorPhysicalEdges
import GafniTao.FordZeroDetectorHorizontalLog

/-!
# Independently selected physical edges for Ford's detector

This is the exact change of variables and vertical Abel identity for an
asymmetric rectangle with physical heights `yLower` and `yUpper`.
-/

open Complex Set MeasureTheory
open RiemannZeta.GuthMaynard
open scoped BigOperators

namespace GafniTao

noncomputable section

def fordDetectorPhysicalScale (eta t y : ℝ) : ℝ :=
  Real.pi * (y - t) / (2 * eta)

def fordDetectorPhysicalVerticalBulk
    (eta t : ℝ) (side : ℂ) (yLower yUpper : ℝ) : ℝ :=
  (1 / (4 * eta)) *
    ∫ u in fordDetectorPhysicalScale eta t yLower..
        fordDetectorPhysicalScale eta t yUpper,
      Real.log ‖riemannZeta
        (fordDetectorCenter t + side +
          (2 * eta * u / Real.pi : ℝ) * I)‖ /
        Real.cosh u ^ 2

def fordDetectorPhysicalResidueMass
    (eta t yLower yUpper : ℝ) : ℂ :=
  fordDetectorZetaLogDeriv (fordDetectorCenter t) -
      fordCotKernel eta (1 - fordDetectorCenter t) +
    ∑ rho ∈ fordDetectorPhysicalZeros eta yLower yUpper,
      (analyticVanishingOrder riemannZeta rho : ℂ) *
        fordCotKernel eta (rho - fordDetectorCenter t)

theorem fordDetector_physicalScale_eq_div
    {eta t y : ℝ} (heta : 0 < eta) :
    (y - t) / (2 * eta / Real.pi) =
      fordDetectorPhysicalScale eta t y := by
  unfold fordDetectorPhysicalScale
  field_simp [heta.ne', Real.pi_ne_zero]

theorem fordDetector_physicalScale_unscale
    {eta t y : ℝ} (heta : 0 < eta) :
    t + 2 * eta * fordDetectorPhysicalScale eta t y / Real.pi = y := by
  unfold fordDetectorPhysicalScale
  field_simp [heta.ne', Real.pi_ne_zero]
  ring

theorem VIntegral'_eq_scaled_physical_param
    (F : ℂ → ℂ) {x t yLower yUpper scale : ℝ} (hscale : scale ≠ 0) :
    VIntegral' F x yLower yUpper =
      ∫ u in (yLower - t) / scale..(yUpper - t) / scale,
        (1 / (2 * (Real.pi : ℂ) * I)) *
          (I * (scale : ℂ)) *
          F ((x : ℂ) + (t + scale * u : ℝ) * I) := by
  let f : ℝ → ℂ := fun y =>
    (1 / (2 * (Real.pi : ℂ) * I)) * I *
      F ((x : ℂ) + (y : ℝ) * I)
  have hchange := intervalIntegral.integral_comp_mul_add
    (f := f) (a := (yLower - t) / scale)
      (b := (yUpper - t) / scale) hscale t
  have hlower : scale * ((yLower - t) / scale) + t = yLower := by
    field_simp [hscale]
    ring
  have hupper : scale * ((yUpper - t) / scale) + t = yUpper := by
    field_simp [hscale]
    ring
  rw [hlower, hupper] at hchange
  have hscaleC : (scale : ℂ) ≠ 0 := by exact_mod_cast hscale
  calc
    VIntegral' F x yLower yUpper =
        ∫ y in yLower..yUpper, f y := by
      unfold VIntegral' VIntegral
      simp only [smul_eq_mul]
      rw [← intervalIntegral.integral_const_mul]
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro y _hy
      dsimp only [f]
      ring_nf
    _ = (scale : ℂ) *
        ∫ u in (yLower - t) / scale..(yUpper - t) / scale,
          f (scale * u + t) := by
      rw [hchange, Complex.real_smul]
      push_cast
      field_simp [hscaleC]
    _ = ∫ u in (yLower - t) / scale..(yUpper - t) / scale,
        (scale : ℂ) * f (scale * u + t) := by
      symm
      exact intervalIntegral.integral_const_mul
        (scale : ℂ) (fun u : ℝ => f (scale * u + t))
    _ = ∫ u in (yLower - t) / scale..(yUpper - t) / scale,
        (1 / (2 * (Real.pi : ℂ) * I)) *
          (I * (scale : ℂ)) *
          F ((x : ℂ) + (t + scale * u : ℝ) * I) := by
      apply intervalIntegral.integral_congr
      intro u _hu
      dsimp only [f]
      push_cast
      ring_nf

theorem re_VIntegral'_eq_integral_re_scaled_physical_param
    (F : ℂ → ℂ) {x t yLower yUpper scale : ℝ} (hscale : scale ≠ 0)
    (hint : IntervalIntegrable
      (fun u : ℝ =>
        (1 / (2 * (Real.pi : ℂ) * I)) *
          (I * (scale : ℂ)) *
          F ((x : ℂ) + (t + scale * u : ℝ) * I))
      volume ((yLower - t) / scale) ((yUpper - t) / scale)) :
    (VIntegral' F x yLower yUpper).re =
      ∫ u in (yLower - t) / scale..(yUpper - t) / scale,
        ((1 / (2 * (Real.pi : ℂ) * I)) *
          (I * (scale : ℂ)) *
          F ((x : ℂ) + (t + scale * u : ℝ) * I)).re := by
  rw [VIntegral'_eq_scaled_physical_param F hscale]
  exact (intervalIntegral.intervalIntegral_re hint).symm

theorem re_fordZetaDetector_physicalVerticalEdge_eq_logIntegral
    {eta t yLower yUpper : ℝ} (heta : 0 < eta) (side : ℝ)
    (hkernel : ∀ u : ℝ,
      fordCotKernel eta
        ((side : ℂ) + (2 * eta * u / Real.pi : ℝ) * I) =
      -((Real.pi / (2 * eta) : ℝ) : ℂ) *
        (Real.tanh u : ℂ) * I)
    (h1 : ∀ u ∈ uIcc (fordDetectorPhysicalScale eta t yLower)
        (fordDetectorPhysicalScale eta t yUpper),
      fordDetectorCenter t + (side : ℂ) +
          (2 * eta * u / Real.pi : ℝ) * I ≠ 1)
    (hzeta : ∀ u ∈ uIcc (fordDetectorPhysicalScale eta t yLower)
        (fordDetectorPhysicalScale eta t yUpper),
      riemannZeta (fordDetectorCenter t + (side : ℂ) +
        (2 * eta * u / Real.pi : ℝ) * I) ≠ 0) :
    (VIntegral' (fordZetaDetectorIntegrand eta (fordDetectorCenter t))
        (1 + side) yLower yUpper).re =
      (1 / (4 * eta)) *
        ((∫ u in fordDetectorPhysicalScale eta t yLower..
            fordDetectorPhysicalScale eta t yUpper,
          Real.log ‖riemannZeta
            (fordDetectorCenter t + (side : ℂ) +
              (2 * eta * u / Real.pi : ℝ) * I)‖ /
            Real.cosh u ^ 2) -
          (Real.tanh (fordDetectorPhysicalScale eta t yUpper) *
              Real.log ‖riemannZeta
                (fordDetectorCenter t + (side : ℂ) +
                  (2 * eta * fordDetectorPhysicalScale eta t yUpper /
                    Real.pi : ℝ) * I)‖ -
           Real.tanh (fordDetectorPhysicalScale eta t yLower) *
              Real.log ‖riemannZeta
                (fordDetectorCenter t + (side : ℂ) +
                  (2 * eta * fordDetectorPhysicalScale eta t yLower /
                    Real.pi : ℝ) * I)‖)) := by
  let scale : ℝ := 2 * eta / Real.pi
  let lo : ℝ := fordDetectorPhysicalScale eta t yLower
  let hi : ℝ := fordDetectorPhysicalScale eta t yUpper
  have hscale : scale ≠ 0 := by
    dsimp only [scale]
    exact div_ne_zero (mul_ne_zero two_ne_zero heta.ne') Real.pi_ne_zero
  have hlo : (yLower - t) / scale = lo := by
    dsimp only [lo, scale]
    exact fordDetector_physicalScale_eq_div heta
  have hhi : (yUpper - t) / scale = hi := by
    dsimp only [hi, scale]
    exact fordDetector_physicalScale_eq_div heta
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
      dsimp only [scale, fordDetectorCenter]
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
    dsimp only [centered, lo, hi]
    exact intervalIntegrable_fordDetector_verticalParam
      (fordDetectorCenter t) side hkernel h1 hzeta
  have hphysicalInt : IntervalIntegrable physical volume lo hi := by
    rw [hpc]
    exact hcenterInt
  have hinput : IntervalIntegrable
      (fun u : ℝ =>
        (1 / (2 * (Real.pi : ℂ) * I)) *
          (I * (scale : ℂ)) *
          fordZetaDetectorIntegrand eta (fordDetectorCenter t)
            (((1 + side : ℝ) : ℂ) + (t + scale * u : ℝ) * I))
      volume ((yLower - t) / scale) ((yUpper - t) / scale) := by
    rw [hlo, hhi]
    change IntervalIntegrable physical volume lo hi
    exact hphysicalInt
  have hV := re_VIntegral'_eq_integral_re_scaled_physical_param
    (fordZetaDetectorIntegrand eta (fordDetectorCenter t))
    (x := 1 + side) (t := t) (yLower := yLower)
    (yUpper := yUpper) (scale := scale) hscale hinput
  have hAbel := integral_re_fordDetector_verticalParam_eq
    heta (fordDetectorCenter t) side hkernel h1 hzeta
  rw [hlo, hhi] at hV
  rw [hV]
  rw [show (fun u : ℝ =>
      ((1 / (2 * (Real.pi : ℂ) * I)) *
        (I * (scale : ℂ)) *
        fordZetaDetectorIntegrand eta (fordDetectorCenter t)
          (((1 + side : ℝ) : ℂ) +
            (t + scale * u : ℝ) * I)).re) =
      fun u => (centered u).re by
    funext u
    rw [← hpc]]
  simpa only [centered, scale, lo, hi] using hAbel

theorem re_fordZetaDetector_physicalRightEdge_eq_logIntegral
    {eta t yLower yUpper : ℝ} (heta : 0 < eta) :
    (VIntegral' (fordZetaDetectorIntegrand eta (fordDetectorCenter t))
        (1 + eta) yLower yUpper).re =
      (1 / (4 * eta)) *
        ((∫ u in fordDetectorPhysicalScale eta t yLower..
            fordDetectorPhysicalScale eta t yUpper,
          Real.log ‖riemannZeta
            (fordDetectorCenter t + (eta : ℂ) +
              (2 * eta * u / Real.pi : ℝ) * I)‖ /
            Real.cosh u ^ 2) -
          (Real.tanh (fordDetectorPhysicalScale eta t yUpper) *
              Real.log ‖riemannZeta
                (fordDetectorCenter t + (eta : ℂ) +
                  (2 * eta * fordDetectorPhysicalScale eta t yUpper /
                    Real.pi : ℝ) * I)‖ -
           Real.tanh (fordDetectorPhysicalScale eta t yLower) *
              Real.log ‖riemannZeta
                (fordDetectorCenter t + (eta : ℂ) +
                  (2 * eta * fordDetectorPhysicalScale eta t yLower /
                    Real.pi : ℝ) * I)‖)) := by
  apply re_fordZetaDetector_physicalVerticalEdge_eq_logIntegral
    heta eta (fordCotKernel_pos_vertical heta)
  · intro u _hu hEq
    have hre := congrArg Complex.re hEq
    simp [fordDetectorCenter] at hre
    linarith
  · intro u _hu
    apply riemannZeta_ne_zero_of_one_le_re
    simp [fordDetectorCenter]
    linarith

theorem re_fordZetaDetector_physicalLeftEdge_eq_logIntegral
    {eta t yLower yUpper : ℝ} (heta : 0 < eta)
    (hzeta : ∀ u ∈ uIcc (fordDetectorPhysicalScale eta t yLower)
        (fordDetectorPhysicalScale eta t yUpper),
      riemannZeta (fordDetectorCenter t + (-eta : ℂ) +
        (2 * eta * u / Real.pi : ℝ) * I) ≠ 0) :
    (VIntegral' (fordZetaDetectorIntegrand eta (fordDetectorCenter t))
        (1 - eta) yLower yUpper).re =
      (1 / (4 * eta)) *
        ((∫ u in fordDetectorPhysicalScale eta t yLower..
            fordDetectorPhysicalScale eta t yUpper,
          Real.log ‖riemannZeta
            (fordDetectorCenter t + (-eta : ℂ) +
              (2 * eta * u / Real.pi : ℝ) * I)‖ /
            Real.cosh u ^ 2) -
          (Real.tanh (fordDetectorPhysicalScale eta t yUpper) *
              Real.log ‖riemannZeta
                (fordDetectorCenter t + (-eta : ℂ) +
                  (2 * eta * fordDetectorPhysicalScale eta t yUpper /
                    Real.pi : ℝ) * I)‖ -
           Real.tanh (fordDetectorPhysicalScale eta t yLower) *
              Real.log ‖riemannZeta
                (fordDetectorCenter t + (-eta : ℂ) +
                  (2 * eta * fordDetectorPhysicalScale eta t yLower /
                    Real.pi : ℝ) * I)‖)) := by
  simpa using
    (re_fordZetaDetector_physicalVerticalEdge_eq_logIntegral
      (eta := eta) (t := t) (yLower := yLower) (yUpper := yUpper)
      heta (-eta)
      (fun u => by simpa using fordCotKernel_neg_vertical heta u)
      (fun u _hu hEq => by
        have hre := congrArg Complex.re hEq
        simp [fordDetectorCenter] at hre
        linarith)
      (fun u hu => by simpa using hzeta u hu))

end

end GafniTao
