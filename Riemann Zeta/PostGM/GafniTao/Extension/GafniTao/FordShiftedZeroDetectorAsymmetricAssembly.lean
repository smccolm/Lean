import GafniTao.FordShiftedZeroDetectorAsymmetricEdges
import GafniTao.FordShiftedZeroDetectorAssembly

/-!
# Finite shifted Abel assembly on independent physical heights

This is the physical-height version of the shifted Ford detector.  In
particular, the zeta pole is an explicit summand of the residue mass.
-/

open Complex Set MeasureTheory
open RiemannZeta.GuthMaynard
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem fordShiftedDetector_physicalVerticalPoint
    (sigma t side y : ℝ) :
    fordShiftedDetectorCenter sigma t + (side : ℂ) +
        (y - t : ℝ) * I =
      fordHorizontalPoint t (y - t) (sigma + side) := by
  unfold fordShiftedDetectorCenter fordHorizontalPoint
  push_cast
  ring

theorem re_fordZetaShiftedDetector_physicalRightEdge_eq_bulk_sub_boundary
    {sigma eta t yLower yUpper : ℝ} (hsigma : 1 ≤ sigma)
    (heta : 0 < eta) :
    (VIntegral'
      (fordZetaDetectorIntegrand eta
        (fordShiftedDetectorCenter sigma t))
      (sigma + eta) yLower yUpper).re =
      fordShiftedDetectorPhysicalVerticalBulk eta sigma t
          (eta : ℂ) yLower yUpper -
        (1 / (4 * eta)) *
          (Real.tanh (fordDetectorPhysicalScale eta t yUpper) *
              fordDetectorEdgeLog t (yUpper - t) (sigma + eta) -
            Real.tanh (fordDetectorPhysicalScale eta t yLower) *
              fordDetectorEdgeLog t (yLower - t) (sigma + eta)) := by
  rw [re_fordZetaShiftedDetector_physicalRightEdge_eq_logIntegral
    hsigma heta]
  have hupper := fordDetector_physicalScale_unscale
    (t := t) (y := yUpper) heta
  have hlower := fordDetector_physicalScale_unscale
    (t := t) (y := yLower) heta
  change _ =
    fordShiftedDetectorPhysicalVerticalBulk eta sigma t
      (eta : ℂ) yLower yUpper - _
  unfold fordShiftedDetectorPhysicalVerticalBulk fordDetectorEdgeLog
  have htop :
      fordShiftedDetectorCenter sigma t + (eta : ℂ) +
          (2 * eta * fordDetectorPhysicalScale eta t yUpper /
            Real.pi : ℝ) * I =
        fordHorizontalPoint t (yUpper - t) (sigma + eta) := by
    rw [show 2 * eta * fordDetectorPhysicalScale eta t yUpper /
      Real.pi = yUpper - t by linarith]
    exact fordShiftedDetector_physicalVerticalPoint sigma t eta yUpper
  have hbottom :
      fordShiftedDetectorCenter sigma t + (eta : ℂ) +
          (2 * eta * fordDetectorPhysicalScale eta t yLower /
            Real.pi : ℝ) * I =
        fordHorizontalPoint t (yLower - t) (sigma + eta) := by
    rw [show 2 * eta * fordDetectorPhysicalScale eta t yLower /
      Real.pi = yLower - t by linarith]
    exact fordShiftedDetector_physicalVerticalPoint sigma t eta yLower
  rw [htop, hbottom]
  ring

theorem re_fordZetaShiftedDetector_physicalLeftEdge_eq_bulk_sub_boundary
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
      fordShiftedDetectorPhysicalVerticalBulk eta sigma t
          (-eta : ℂ) yLower yUpper -
        (1 / (4 * eta)) *
          (Real.tanh (fordDetectorPhysicalScale eta t yUpper) *
              fordDetectorEdgeLog t (yUpper - t) (sigma - eta) -
            Real.tanh (fordDetectorPhysicalScale eta t yLower) *
              fordDetectorEdgeLog t (yLower - t) (sigma - eta)) := by
  rw [re_fordZetaShiftedDetector_physicalLeftEdge_eq_logIntegral
    heta hleftOne hzeta]
  have hupper := fordDetector_physicalScale_unscale
    (t := t) (y := yUpper) heta
  have hlower := fordDetector_physicalScale_unscale
    (t := t) (y := yLower) heta
  change _ =
    fordShiftedDetectorPhysicalVerticalBulk eta sigma t
      (-eta : ℂ) yLower yUpper - _
  unfold fordShiftedDetectorPhysicalVerticalBulk fordDetectorEdgeLog
  have htop :
      fordShiftedDetectorCenter sigma t + (-eta : ℂ) +
          (2 * eta * fordDetectorPhysicalScale eta t yUpper /
            Real.pi : ℝ) * I =
        fordHorizontalPoint t (yUpper - t) (sigma - eta) := by
    rw [show 2 * eta * fordDetectorPhysicalScale eta t yUpper /
      Real.pi = yUpper - t by linarith]
    unfold fordShiftedDetectorCenter fordHorizontalPoint
    push_cast
    ring
  have hbottom :
      fordShiftedDetectorCenter sigma t + (-eta : ℂ) +
          (2 * eta * fordDetectorPhysicalScale eta t yLower /
            Real.pi : ℝ) * I =
        fordHorizontalPoint t (yLower - t) (sigma - eta) := by
    rw [show 2 * eta * fordDetectorPhysicalScale eta t yLower /
      Real.pi = yLower - t by linarith]
    unfold fordShiftedDetectorCenter fordHorizontalPoint
    push_cast
    ring
  rw [htop, hbottom]
  ring

theorem fordZetaShiftedDetector_physicalRightEdge_eq_explicit_add_edges
    {sigma eta t yLower yUpper : ℝ} (hsigma : 1 ≤ sigma)
    (heta : 0 < eta) (ht : 0 < t) (hPole : sigma - 1 < eta)
    (hyLower : yLower < 0) (hytLower : yLower < t)
    (hytUpper : t < yUpper) (hleft : -1 ≤ sigma - eta)
    (hboundary : ∀ rho ∈
      fordShiftedDetectorPhysicalZeros sigma eta yLower yUpper,
      |rho.re - sigma| < eta ∧
        yLower < rho.im ∧ rho.im < yUpper) :
    VIntegral'
      (fordZetaDetectorIntegrand eta
        (fordShiftedDetectorCenter sigma t))
      (sigma + eta) yLower yUpper =
      fordShiftedDetectorPhysicalResidueMass
          sigma eta t yLower yUpper -
        HIntegral'
          (fordZetaDetectorIntegrand eta
            (fordShiftedDetectorCenter sigma t))
          (sigma - eta) (sigma + eta) yLower +
        HIntegral'
          (fordZetaDetectorIntegrand eta
            (fordShiftedDetectorCenter sigma t))
          (sigma - eta) (sigma + eta) yUpper +
        VIntegral'
          (fordZetaDetectorIntegrand eta
            (fordShiftedDetectorCenter sigma t))
          (sigma - eta) yLower yUpper := by
  have hrect :=
    fordZetaShiftedDetector_physicalRectangleIntegral_eq_explicit_sum
      hsigma heta ht hPole hyLower hytLower hytUpper hleft hboundary
  have hreLower :
      (fordShiftedDetectorPhysicalLower sigma eta yLower).re =
        sigma - eta := by
    simp [fordShiftedDetectorPhysicalLower]
  have hreUpper :
      (fordShiftedDetectorPhysicalUpper sigma eta yUpper).re =
        sigma + eta := by
    simp [fordShiftedDetectorPhysicalUpper]
  have himLower :
      (fordShiftedDetectorPhysicalLower sigma eta yLower).im =
        yLower := by
    simp [fordShiftedDetectorPhysicalLower]
  have himUpper :
      (fordShiftedDetectorPhysicalUpper sigma eta yUpper).im =
        yUpper := by
    simp [fordShiftedDetectorPhysicalUpper]
  change RectangleIntegral'
      (fordZetaDetectorIntegrand eta
        (fordShiftedDetectorCenter sigma t))
      (fordShiftedDetectorPhysicalLower sigma eta yLower)
      (fordShiftedDetectorPhysicalUpper sigma eta yUpper) =
    fordShiftedDetectorPhysicalResidueMass
      sigma eta t yLower yUpper at hrect
  simp only [RectangleIntegral', RectangleIntegral, HIntegral', VIntegral',
    smul_eq_mul] at hrect ⊢
  rw [hreLower, hreUpper, himLower, himUpper] at hrect
  linear_combination hrect

/-- Exact finite shifted Abel formula on independently selected heights. -/
theorem re_fordShiftedDetectorPhysicalResidueMass_eq_finite_abel
    {sigma eta t yLower yUpper : ℝ} (hsigma : 1 ≤ sigma)
    (heta : 0 < eta) (ht : 0 < t) (hPole : sigma - 1 < eta)
    (hyLower : yLower < 0) (hytLower : yLower < t)
    (hytUpper : t < yUpper) (hleft : -1 ≤ sigma - eta)
    (hleftOne : sigma - eta ≠ 1)
    (hboundary : ∀ rho ∈
      fordShiftedDetectorPhysicalZeros sigma eta yLower yUpper,
      |rho.re - sigma| < eta ∧
        yLower < rho.im ∧ rho.im < yUpper)
    (hzetaLeft : ∀ u ∈ uIcc
        (fordDetectorPhysicalScale eta t yLower)
        (fordDetectorPhysicalScale eta t yUpper),
      riemannZeta
        (fordShiftedDetectorCenter sigma t + (-eta : ℂ) +
          (2 * eta * u / Real.pi : ℝ) * I) ≠ 0)
    (hzetaTop : ∀ x : ℝ,
      riemannZeta (fordHorizontalPoint t (yUpper - t) x) ≠ 0)
    (hzetaBottom : ∀ x : ℝ,
      riemannZeta (fordHorizontalPoint t (yLower - t) x) ≠ 0) :
    (fordShiftedDetectorPhysicalResidueMass
        sigma eta t yLower yUpper).re =
      fordShiftedDetectorPhysicalVerticalBulk eta sigma t
          (eta : ℂ) yLower yUpper -
        fordShiftedDetectorPhysicalVerticalBulk eta sigma t
          (-eta : ℂ) yLower yUpper -
        (fordShiftedHorizontalRemainder
          sigma eta t (yLower - t)).re +
        (fordShiftedHorizontalRemainder
          sigma eta t (yUpper - t)).re := by
  have htopOffset : yUpper - t ≠ 0 := sub_ne_zero.mpr hytUpper.ne'
  have hbottomOffset : yLower - t ≠ 0 := sub_ne_zero.mpr hytLower.ne
  have htopIm : t + (yUpper - t) ≠ 0 := by linarith
  have hbottomIm : t + (yLower - t) ≠ 0 := by linarith
  have htop1 : ∀ x : ℝ,
      fordHorizontalPoint t (yUpper - t) x ≠ 1 :=
    fun _x => fordHorizontalPoint_ne_one_of_im_ne_zero htopIm
  have hbottom1 : ∀ x : ℝ,
      fordHorizontalPoint t (yLower - t) x ≠ 1 :=
    fun _x => fordHorizontalPoint_ne_one_of_im_ne_zero hbottomIm
  have hedge :=
    fordZetaShiftedDetector_physicalRightEdge_eq_explicit_add_edges
      hsigma heta ht hPole hyLower hytLower hytUpper hleft hboundary
  have hre := congrArg Complex.re hedge
  simp only [Complex.add_re, Complex.sub_re] at hre
  rw [re_fordZetaShiftedDetector_physicalRightEdge_eq_bulk_sub_boundary
      hsigma heta,
    re_fordZetaShiftedDetector_physicalLeftEdge_eq_bulk_sub_boundary
      heta hleftOne hzetaLeft] at hre
  have htopHeight : yUpper = t + (yUpper - t) := by ring
  rw [htopHeight,
    re_HIntegral'_fordZetaShiftedDetector_eq_boundary_sub_remainder
      heta htopOffset htop1 hzetaTop] at hre
  have hbottomHeight : yLower = t + (yLower - t) := by ring
  rw [hbottomHeight,
    re_HIntegral'_fordZetaShiftedDetector_eq_boundary_sub_remainder
      heta hbottomOffset hbottom1 hzetaBottom] at hre
  have htopRestore : t + (yUpper - t) = yUpper := by ring
  have hbottomRestore : t + (yLower - t) = yLower := by ring
  rw [htopRestore, hbottomRestore] at hre
  rw [show fordDetectorScaledHeight eta (yUpper - t) =
      fordDetectorPhysicalScale eta t yUpper by rfl,
    show fordDetectorScaledHeight eta (yLower - t) =
      fordDetectorPhysicalScale eta t yLower by rfl] at hre
  linear_combination -hre

end

end GafniTao
