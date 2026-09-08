import GafniTao.FordShiftedZeroDetectorFinite
import GafniTao.FordZeroDetectorPhysicalEdges
import GafniTao.FordZeroDetectorAbelAssembly

/-!
# Vertical logarithm identities for the shifted Ford detector
-/

open Complex Set MeasureTheory
open RiemannZeta.GuthMaynard

namespace GafniTao

noncomputable section

def fordShiftedDetectorVerticalBulk
    (eta sigma t side R : ℝ) : ℝ :=
  (1 / (4 * eta)) *
    ∫ u in (-fordDetectorScaledHeight eta R)..
        (fordDetectorScaledHeight eta R),
      Real.log ‖riemannZeta
        (fordShiftedDetectorCenter sigma t + (side : ℂ) +
          (2 * eta * u / Real.pi : ℝ) * I)‖ /
        Real.cosh u ^ 2

theorem re_fordZetaShiftedDetector_verticalEdge_eq_logIntegral
    {sigma eta t R : ℝ} (heta : 0 < eta) (side : ℝ)
    (hkernel : ∀ u : ℝ,
      fordCotKernel eta
        ((side : ℂ) + (2 * eta * u / Real.pi : ℝ) * I) =
      -((Real.pi / (2 * eta) : ℝ) : ℂ) *
        (Real.tanh u : ℂ) * I)
    (h1 : ∀ u ∈ uIcc (-R / (2 * eta / Real.pi))
        (R / (2 * eta / Real.pi)),
      fordShiftedDetectorCenter sigma t + (side : ℂ) +
          (2 * eta * u / Real.pi : ℝ) * I ≠ 1)
    (hzeta : ∀ u ∈ uIcc (-R / (2 * eta / Real.pi))
        (R / (2 * eta / Real.pi)),
      riemannZeta (fordShiftedDetectorCenter sigma t + (side : ℂ) +
        (2 * eta * u / Real.pi : ℝ) * I) ≠ 0) :
    (VIntegral'
      (fordZetaDetectorIntegrand eta
        (fordShiftedDetectorCenter sigma t))
      (sigma + side) (t - R) (t + R)).re =
      (1 / (4 * eta)) *
        ((∫ u in (-R / (2 * eta / Real.pi))..
            (R / (2 * eta / Real.pi)),
          Real.log ‖riemannZeta
            (fordShiftedDetectorCenter sigma t + (side : ℂ) +
              (2 * eta * u / Real.pi : ℝ) * I)‖ /
            Real.cosh u ^ 2) -
          (Real.tanh (R / (2 * eta / Real.pi)) *
              Real.log ‖riemannZeta
                (fordShiftedDetectorCenter sigma t + (side : ℂ) +
                  (2 * eta * (R / (2 * eta / Real.pi)) /
                    Real.pi : ℝ) * I)‖ -
           Real.tanh (-R / (2 * eta / Real.pi)) *
              Real.log ‖riemannZeta
                (fordShiftedDetectorCenter sigma t + (side : ℂ) +
                  (2 * eta * (-R / (2 * eta / Real.pi)) /
                    Real.pi : ℝ) * I)‖)) := by
  let scale : ℝ := 2 * eta / Real.pi
  let lo : ℝ := -R / scale
  let hi : ℝ := R / scale
  have hscale : scale ≠ 0 := by
    dsimp only [scale]
    exact div_ne_zero (mul_ne_zero two_ne_zero heta.ne') Real.pi_ne_zero
  have hlo : lo = -R / (2 * eta / Real.pi) := rfl
  have hhi : hi = R / (2 * eta / Real.pi) := rfl
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
          (side : ℂ) + (2 * eta * u / Real.pi : ℝ) * I := by
      ring
    dsimp only [physical, centered, fordZetaDetectorIntegrand]
    rw [hs, hsub]
    dsimp only [scale]
    ring
  have hcenterInt : IntervalIntegrable centered volume lo hi := by
    dsimp only [centered, lo, hi, scale]
    exact intervalIntegrable_fordDetector_verticalParam
      (fordShiftedDetectorCenter sigma t) side hkernel h1 hzeta
  have hphysicalInt : IntervalIntegrable physical volume lo hi := by
    rw [hpc]
    exact hcenterInt
  have hV := re_VIntegral'_eq_integral_re_scaled_param
    (fordZetaDetectorIntegrand eta
      (fordShiftedDetectorCenter sigma t))
    (x := sigma + side) (t := t) (R := R) (scale := scale)
    hscale hphysicalInt
  have hAbel := integral_re_fordDetector_verticalParam_eq
    heta (fordShiftedDetectorCenter sigma t) side hkernel h1 hzeta
  dsimp only [lo, hi] at hcenterInt hphysicalInt
  dsimp only [scale] at hV ⊢
  rw [hV]
  rw [show (fun u : ℝ =>
      ((1 / (2 * (Real.pi : ℂ) * I)) *
        (I * ((2 * eta / Real.pi : ℝ) : ℂ)) *
        fordZetaDetectorIntegrand eta
          (fordShiftedDetectorCenter sigma t)
          (((sigma + side : ℝ) : ℂ) +
            (t + (2 * eta / Real.pi) * u : ℝ) * I)).re) =
      fun u => (centered u).re by
        funext u
        rw [← hpc]]
  simpa only [centered, scale, lo, hi] using hAbel

theorem re_fordZetaShiftedDetector_rightEdge_eq_logIntegral
    {sigma eta t R : ℝ} (hsigma : 1 ≤ sigma) (heta : 0 < eta) :
    (VIntegral'
      (fordZetaDetectorIntegrand eta
        (fordShiftedDetectorCenter sigma t))
      (sigma + eta) (t - R) (t + R)).re =
      (1 / (4 * eta)) *
        ((∫ u in (-R / (2 * eta / Real.pi))..
            (R / (2 * eta / Real.pi)),
          Real.log ‖riemannZeta
            (fordShiftedDetectorCenter sigma t + (eta : ℂ) +
              (2 * eta * u / Real.pi : ℝ) * I)‖ /
            Real.cosh u ^ 2) -
          (Real.tanh (R / (2 * eta / Real.pi)) *
              Real.log ‖riemannZeta
                (fordShiftedDetectorCenter sigma t + (eta : ℂ) +
                  (2 * eta * (R / (2 * eta / Real.pi)) /
                    Real.pi : ℝ) * I)‖ -
           Real.tanh (-R / (2 * eta / Real.pi)) *
              Real.log ‖riemannZeta
                (fordShiftedDetectorCenter sigma t + (eta : ℂ) +
                  (2 * eta * (-R / (2 * eta / Real.pi)) /
                    Real.pi : ℝ) * I)‖)) := by
  apply re_fordZetaShiftedDetector_verticalEdge_eq_logIntegral
    heta eta (fordCotKernel_pos_vertical heta)
  · intro u _hu hEq
    have hre := congrArg Complex.re hEq
    simp [fordShiftedDetectorCenter] at hre
    linarith
  · intro u _hu
    apply riemannZeta_ne_zero_of_one_le_re
    simp [fordShiftedDetectorCenter]
    linarith

theorem re_fordZetaShiftedDetector_leftEdge_eq_logIntegral
    {sigma eta t R : ℝ} (heta : 0 < eta)
    (hleftOne : sigma - eta ≠ 1)
    (hzeta : ∀ u ∈ uIcc (-R / (2 * eta / Real.pi))
        (R / (2 * eta / Real.pi)),
      riemannZeta
        (fordShiftedDetectorCenter sigma t + (-eta : ℂ) +
          (2 * eta * u / Real.pi : ℝ) * I) ≠ 0) :
    (VIntegral'
      (fordZetaDetectorIntegrand eta
        (fordShiftedDetectorCenter sigma t))
      (sigma - eta) (t - R) (t + R)).re =
      (1 / (4 * eta)) *
        ((∫ u in (-R / (2 * eta / Real.pi))..
            (R / (2 * eta / Real.pi)),
          Real.log ‖riemannZeta
            (fordShiftedDetectorCenter sigma t + (-eta : ℂ) +
              (2 * eta * u / Real.pi : ℝ) * I)‖ /
            Real.cosh u ^ 2) -
          (Real.tanh (R / (2 * eta / Real.pi)) *
              Real.log ‖riemannZeta
                (fordShiftedDetectorCenter sigma t + (-eta : ℂ) +
                  (2 * eta * (R / (2 * eta / Real.pi)) /
                    Real.pi : ℝ) * I)‖ -
           Real.tanh (-R / (2 * eta / Real.pi)) *
              Real.log ‖riemannZeta
                (fordShiftedDetectorCenter sigma t + (-eta : ℂ) +
                  (2 * eta * (-R / (2 * eta / Real.pi)) /
                    Real.pi : ℝ) * I)‖)) := by
  simpa [sub_eq_add_neg] using
    (re_fordZetaShiftedDetector_verticalEdge_eq_logIntegral
      (sigma := sigma) (eta := eta) (t := t) (R := R)
      heta (-eta)
      (fun u => by simpa using fordCotKernel_neg_vertical heta u)
      (fun u _hu hEq => by
        have hre := congrArg Complex.re hEq
        simp [fordShiftedDetectorCenter] at hre
        exact hleftOne hre)
      (fun u hu => by simpa using hzeta u hu))

end

end GafniTao
