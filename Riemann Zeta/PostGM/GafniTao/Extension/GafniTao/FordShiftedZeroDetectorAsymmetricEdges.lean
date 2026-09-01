import GafniTao.FordShiftedZeroDetectorAsymmetricRectangle
import GafniTao.FordZeroDetectorAsymmetricEdges

/-!
# Independent physical edges for the shifted Ford detector
-/

open Complex Set MeasureTheory
open RiemannZeta.GuthMaynard
open scoped BigOperators

namespace GafniTao

noncomputable section

def fordShiftedDetectorPhysicalVerticalBulk
    (eta sigma t : ℝ) (side : ℂ) (yLower yUpper : ℝ) : ℝ :=
  (1 / (4 * eta)) *
    ∫ u in fordDetectorPhysicalScale eta t yLower..
        fordDetectorPhysicalScale eta t yUpper,
      Real.log ‖riemannZeta
        (fordShiftedDetectorCenter sigma t + side +
          (2 * eta * u / Real.pi : ℝ) * I)‖ /
        Real.cosh u ^ 2

def fordShiftedDetectorPhysicalResidueMass
    (sigma eta t yLower yUpper : ℝ) : ℂ :=
  fordDetectorZetaLogDeriv (fordShiftedDetectorCenter sigma t) -
      fordCotKernel eta (1 - fordShiftedDetectorCenter sigma t) +
    ∑ rho ∈ fordShiftedDetectorPhysicalZeros
        sigma eta yLower yUpper,
      (analyticVanishingOrder riemannZeta rho : ℂ) *
        fordCotKernel eta
          (rho - fordShiftedDetectorCenter sigma t)

theorem re_fordZetaShiftedDetector_physicalVerticalEdge_eq_logIntegral
    {sigma eta t yLower yUpper : ℝ} (heta : 0 < eta) (side : ℝ)
    (hkernel : ∀ u : ℝ,
      fordCotKernel eta
        ((side : ℂ) + (2 * eta * u / Real.pi : ℝ) * I) =
      -((Real.pi / (2 * eta) : ℝ) : ℂ) *
        (Real.tanh u : ℂ) * I)
    (h1 : ∀ u ∈ uIcc (fordDetectorPhysicalScale eta t yLower)
        (fordDetectorPhysicalScale eta t yUpper),
      fordShiftedDetectorCenter sigma t + (side : ℂ) +
          (2 * eta * u / Real.pi : ℝ) * I ≠ 1)
    (hzeta : ∀ u ∈ uIcc (fordDetectorPhysicalScale eta t yLower)
        (fordDetectorPhysicalScale eta t yUpper),
      riemannZeta
        (fordShiftedDetectorCenter sigma t + (side : ℂ) +
          (2 * eta * u / Real.pi : ℝ) * I) ≠ 0) :
    (VIntegral'
      (fordZetaDetectorIntegrand eta
        (fordShiftedDetectorCenter sigma t))
      (sigma + side) yLower yUpper).re =
      (1 / (4 * eta)) *
        ((∫ u in fordDetectorPhysicalScale eta t yLower..
            fordDetectorPhysicalScale eta t yUpper,
          Real.log ‖riemannZeta
            (fordShiftedDetectorCenter sigma t + (side : ℂ) +
              (2 * eta * u / Real.pi : ℝ) * I)‖ /
            Real.cosh u ^ 2) -
          (Real.tanh (fordDetectorPhysicalScale eta t yUpper) *
              Real.log ‖riemannZeta
                (fordShiftedDetectorCenter sigma t + (side : ℂ) +
                  (2 * eta * fordDetectorPhysicalScale eta t yUpper /
                    Real.pi : ℝ) * I)‖ -
           Real.tanh (fordDetectorPhysicalScale eta t yLower) *
              Real.log ‖riemannZeta
                (fordShiftedDetectorCenter sigma t + (side : ℂ) +
                  (2 * eta * fordDetectorPhysicalScale eta t yLower /
                    Real.pi : ℝ) * I)‖)) := by
  let scale : ℝ := 2 * eta / Real.pi
  let lo : ℝ := fordDetectorPhysicalScale eta t yLower
  let hi : ℝ := fordDetectorPhysicalScale eta t yUpper
  have hscale : scale ≠ 0 := by
    dsimp only [scale]
    exact div_ne_zero (mul_ne_zero two_ne_zero heta.ne') Real.pi_ne_zero
  have hlo : lo = (yLower - t) / scale := by
    dsimp only [lo, scale, fordDetectorPhysicalScale]
    field_simp [heta.ne', Real.pi_ne_zero]
  have hhi : hi = (yUpper - t) / scale := by
    dsimp only [hi, scale, fordDetectorPhysicalScale]
    field_simp [heta.ne', Real.pi_ne_zero]
  let centered : ℝ → ℂ := fun u =>
    (1 / (2 * (Real.pi : ℂ) * I)) *
      (I * ((2 * eta / Real.pi : ℝ) : ℂ)) *
      fordCotKernel eta
        ((side : ℂ) + (2 * eta * u / Real.pi : ℝ) * I) *
      fordDetectorZetaLogDeriv
        (fordShiftedDetectorCenter sigma t + (side : ℂ) +
          (2 * eta * u / Real.pi : ℝ) * I)
  let physical : ℝ → ℂ := fun u =>
    (1 / (2 * (Real.pi : ℂ) * I)) *
      (I * (scale : ℂ)) *
      fordZetaDetectorIntegrand eta
        (fordShiftedDetectorCenter sigma t)
        (((sigma + side : ℝ) : ℂ) +
          (t + scale * u : ℝ) * I)
  have hpc : physical = centered := by
    funext u
    have hs :
        (((sigma + side : ℝ) : ℂ) +
            (t + scale * u : ℝ) * I) =
          fordShiftedDetectorCenter sigma t + (side : ℂ) +
            (2 * eta * u / Real.pi : ℝ) * I := by
      dsimp only [scale, fordShiftedDetectorCenter]
      push_cast
      ring
    have hsub :
        (fordShiftedDetectorCenter sigma t + (side : ℂ) +
            (2 * eta * u / Real.pi : ℝ) * I) -
            fordShiftedDetectorCenter sigma t =
          (side : ℂ) + (2 * eta * u / Real.pi : ℝ) * I := by ring
    dsimp only [physical, centered, fordZetaDetectorIntegrand]
    rw [hs, hsub]
    dsimp only [scale]
    ring
  have hcenterInt : IntervalIntegrable centered volume lo hi := by
    dsimp only [centered, lo, hi]
    exact intervalIntegrable_fordDetector_verticalParam
      (fordShiftedDetectorCenter sigma t) side hkernel h1 hzeta
  have hphysicalInt : IntervalIntegrable physical volume lo hi := by
    rw [hpc]
    exact hcenterInt
  have hinput : IntervalIntegrable
      (fun u : ℝ =>
        (1 / (2 * (Real.pi : ℂ) * I)) *
          (I * (scale : ℂ)) *
          fordZetaDetectorIntegrand eta
            (fordShiftedDetectorCenter sigma t)
            (((sigma + side : ℝ) : ℂ) +
              (t + scale * u : ℝ) * I))
      volume ((yLower - t) / scale) ((yUpper - t) / scale) := by
    rw [← hlo, ← hhi]
    change IntervalIntegrable physical volume lo hi
    exact hphysicalInt
  have hV := re_VIntegral'_eq_integral_re_scaled_physical_param
    (fordZetaDetectorIntegrand eta
      (fordShiftedDetectorCenter sigma t))
    (x := sigma + side) (t := t) (yLower := yLower)
    (yUpper := yUpper) (scale := scale) hscale hinput
  have hAbel := integral_re_fordDetector_verticalParam_eq
    heta (fordShiftedDetectorCenter sigma t) side hkernel h1 hzeta
  rw [← hlo, ← hhi] at hV
  rw [hV]
  rw [show (fun u : ℝ =>
      ((1 / (2 * (Real.pi : ℂ) * I)) *
        (I * (scale : ℂ)) *
        fordZetaDetectorIntegrand eta
          (fordShiftedDetectorCenter sigma t)
          (((sigma + side : ℝ) : ℂ) +
            (t + scale * u : ℝ) * I)).re) =
      fun u => (centered u).re by
        funext u
        rw [← hpc]]
  simpa only [centered, scale, lo, hi] using hAbel

theorem re_fordZetaShiftedDetector_physicalRightEdge_eq_logIntegral
    {sigma eta t yLower yUpper : ℝ} (hsigma : 1 ≤ sigma)
    (heta : 0 < eta) :
    (VIntegral'
      (fordZetaDetectorIntegrand eta
        (fordShiftedDetectorCenter sigma t))
      (sigma + eta) yLower yUpper).re =
      (1 / (4 * eta)) *
        ((∫ u in fordDetectorPhysicalScale eta t yLower..
            fordDetectorPhysicalScale eta t yUpper,
          Real.log ‖riemannZeta
            (fordShiftedDetectorCenter sigma t + (eta : ℂ) +
              (2 * eta * u / Real.pi : ℝ) * I)‖ /
            Real.cosh u ^ 2) -
          (Real.tanh (fordDetectorPhysicalScale eta t yUpper) *
              Real.log ‖riemannZeta
                (fordShiftedDetectorCenter sigma t + (eta : ℂ) +
                  (2 * eta * fordDetectorPhysicalScale eta t yUpper /
                    Real.pi : ℝ) * I)‖ -
           Real.tanh (fordDetectorPhysicalScale eta t yLower) *
              Real.log ‖riemannZeta
                (fordShiftedDetectorCenter sigma t + (eta : ℂ) +
                  (2 * eta * fordDetectorPhysicalScale eta t yLower /
                    Real.pi : ℝ) * I)‖)) := by
  apply re_fordZetaShiftedDetector_physicalVerticalEdge_eq_logIntegral
    heta eta (fordCotKernel_pos_vertical heta)
  · intro u _hu hEq
    have hre := congrArg Complex.re hEq
    simp [fordShiftedDetectorCenter] at hre
    linarith
  · intro u _hu
    apply riemannZeta_ne_zero_of_one_le_re
    simp [fordShiftedDetectorCenter]
    linarith

theorem re_fordZetaShiftedDetector_physicalLeftEdge_eq_logIntegral
    {sigma eta t yLower yUpper : ℝ} (heta : 0 < eta)
    (hleftOne : sigma - eta ≠ 1)
    (hzeta : ∀ u ∈ uIcc (fordDetectorPhysicalScale eta t yLower)
        (fordDetectorPhysicalScale eta t yUpper),
      riemannZeta
        (fordShiftedDetectorCenter sigma t + (-eta : ℂ) +
          (2 * eta * u / Real.pi : ℝ) * I) ≠ 0) :
    (VIntegral'
      (fordZetaDetectorIntegrand eta
        (fordShiftedDetectorCenter sigma t))
      (sigma - eta) yLower yUpper).re =
      (1 / (4 * eta)) *
        ((∫ u in fordDetectorPhysicalScale eta t yLower..
            fordDetectorPhysicalScale eta t yUpper,
          Real.log ‖riemannZeta
            (fordShiftedDetectorCenter sigma t + (-eta : ℂ) +
              (2 * eta * u / Real.pi : ℝ) * I)‖ /
            Real.cosh u ^ 2) -
          (Real.tanh (fordDetectorPhysicalScale eta t yUpper) *
              Real.log ‖riemannZeta
                (fordShiftedDetectorCenter sigma t + (-eta : ℂ) +
                  (2 * eta * fordDetectorPhysicalScale eta t yUpper /
                    Real.pi : ℝ) * I)‖ -
           Real.tanh (fordDetectorPhysicalScale eta t yLower) *
              Real.log ‖riemannZeta
                (fordShiftedDetectorCenter sigma t + (-eta : ℂ) +
                  (2 * eta * fordDetectorPhysicalScale eta t yLower /
                    Real.pi : ℝ) * I)‖)) := by
  simpa [sub_eq_add_neg] using
    (re_fordZetaShiftedDetector_physicalVerticalEdge_eq_logIntegral
      (sigma := sigma) (eta := eta) (t := t)
      (yLower := yLower) (yUpper := yUpper)
      heta (-eta)
      (fun u => by simpa using fordCotKernel_neg_vertical heta u)
      (fun u _hu hEq => by
        have hre := congrArg Complex.re hEq
        simp [fordShiftedDetectorCenter] at hre
        exact hleftOne hre)
      (fun u hu => by simpa using hzeta u hu))

end

end GafniTao
