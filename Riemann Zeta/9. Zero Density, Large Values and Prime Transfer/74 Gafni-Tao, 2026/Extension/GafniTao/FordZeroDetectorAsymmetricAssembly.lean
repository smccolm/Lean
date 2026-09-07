import GafniTao.FordZeroDetectorAsymmetricEdges
import GafniTao.FordZeroDetectorAbelAssembly

/-!
# Finite Abel assembly on independent physical heights

All four corner terms cancel without imposing symmetry about the detector
center.  The surviving horizontal terms are the exact normalized logarithm
remainders at the independently selected physical ordinates.
-/

open Complex Set MeasureTheory
open RiemannZeta.GuthMaynard
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem fordDetector_scaledOffset_eq_physicalScale
    (eta t y : ℝ) :
    fordDetectorScaledHeight eta (y - t) =
      fordDetectorPhysicalScale eta t y := by
  rfl

theorem fordDetector_physicalVerticalPoint
    (t side y : ℝ) :
    fordDetectorCenter t + (side : ℂ) +
        (y - t : ℝ) * I =
      fordHorizontalPoint t (y - t) (1 + side) := by
  unfold fordDetectorCenter fordHorizontalPoint
  push_cast
  ring

theorem re_fordZetaDetector_physicalRightEdge_eq_bulk_sub_boundary
    {eta t yLower yUpper : ℝ} (heta : 0 < eta) :
    (VIntegral' (fordZetaDetectorIntegrand eta (fordDetectorCenter t))
        (1 + eta) yLower yUpper).re =
      fordDetectorPhysicalVerticalBulk eta t (eta : ℂ) yLower yUpper -
        (1 / (4 * eta)) *
          (Real.tanh (fordDetectorPhysicalScale eta t yUpper) *
              fordDetectorEdgeLog t (yUpper - t) (1 + eta) -
            Real.tanh (fordDetectorPhysicalScale eta t yLower) *
              fordDetectorEdgeLog t (yLower - t) (1 + eta)) := by
  rw [re_fordZetaDetector_physicalRightEdge_eq_logIntegral heta]
  have hupper := fordDetector_physicalScale_unscale
    (t := t) (y := yUpper) heta
  have hlower := fordDetector_physicalScale_unscale
    (t := t) (y := yLower) heta
  change _ = fordDetectorPhysicalVerticalBulk eta t (eta : ℂ)
    yLower yUpper - _
  unfold fordDetectorPhysicalVerticalBulk fordDetectorEdgeLog
  have htop :
      fordDetectorCenter t + (eta : ℂ) +
          (2 * eta * fordDetectorPhysicalScale eta t yUpper /
            Real.pi : ℝ) * I =
        fordHorizontalPoint t (yUpper - t) (1 + eta) := by
    rw [show 2 * eta * fordDetectorPhysicalScale eta t yUpper /
      Real.pi = yUpper - t by linarith]
    exact fordDetector_physicalVerticalPoint t eta yUpper
  have hbottom :
      fordDetectorCenter t + (eta : ℂ) +
          (2 * eta * fordDetectorPhysicalScale eta t yLower /
            Real.pi : ℝ) * I =
        fordHorizontalPoint t (yLower - t) (1 + eta) := by
    rw [show 2 * eta * fordDetectorPhysicalScale eta t yLower /
      Real.pi = yLower - t by linarith]
    exact fordDetector_physicalVerticalPoint t eta yLower
  rw [htop, hbottom]
  ring

theorem re_fordZetaDetector_physicalLeftEdge_eq_bulk_sub_boundary
    {eta t yLower yUpper : ℝ} (heta : 0 < eta)
    (hzeta : ∀ u ∈ uIcc (fordDetectorPhysicalScale eta t yLower)
        (fordDetectorPhysicalScale eta t yUpper),
      riemannZeta (fordDetectorCenter t + (-eta : ℂ) +
        (2 * eta * u / Real.pi : ℝ) * I) ≠ 0) :
    (VIntegral' (fordZetaDetectorIntegrand eta (fordDetectorCenter t))
        (1 - eta) yLower yUpper).re =
      fordDetectorPhysicalVerticalBulk eta t (-eta : ℂ) yLower yUpper -
        (1 / (4 * eta)) *
          (Real.tanh (fordDetectorPhysicalScale eta t yUpper) *
              fordDetectorEdgeLog t (yUpper - t) (1 - eta) -
            Real.tanh (fordDetectorPhysicalScale eta t yLower) *
              fordDetectorEdgeLog t (yLower - t) (1 - eta)) := by
  rw [re_fordZetaDetector_physicalLeftEdge_eq_logIntegral heta hzeta]
  have hupper := fordDetector_physicalScale_unscale
    (t := t) (y := yUpper) heta
  have hlower := fordDetector_physicalScale_unscale
    (t := t) (y := yLower) heta
  change _ = fordDetectorPhysicalVerticalBulk eta t (-eta : ℂ)
    yLower yUpper - _
  unfold fordDetectorPhysicalVerticalBulk fordDetectorEdgeLog
  have htop :
      fordDetectorCenter t + (-eta : ℂ) +
          (2 * eta * fordDetectorPhysicalScale eta t yUpper /
            Real.pi : ℝ) * I =
        fordHorizontalPoint t (yUpper - t) (1 - eta) := by
    rw [show 2 * eta * fordDetectorPhysicalScale eta t yUpper /
      Real.pi = yUpper - t by linarith]
    unfold fordDetectorCenter fordHorizontalPoint
    push_cast
    ring
  have hbottom :
      fordDetectorCenter t + (-eta : ℂ) +
          (2 * eta * fordDetectorPhysicalScale eta t yLower /
            Real.pi : ℝ) * I =
        fordHorizontalPoint t (yLower - t) (1 - eta) := by
    rw [show 2 * eta * fordDetectorPhysicalScale eta t yLower /
      Real.pi = yLower - t by linarith]
    unfold fordDetectorCenter fordHorizontalPoint
    push_cast
    ring
  rw [htop, hbottom]
  ring

theorem fordZetaDetector_physicalRightEdge_eq_explicit_add_edges
    {eta t yLower yUpper : ℝ} (heta : 0 < eta) (hetaUpper : eta ≤ 1)
    (ht : 0 < t) (hyLower : yLower < 0)
    (hytLower : yLower < t) (hytUpper : t < yUpper)
    (hboundary : ∀ rho ∈ fordDetectorPhysicalZeros eta yLower yUpper,
      |rho.re - 1| < eta ∧ yLower < rho.im ∧ rho.im < yUpper) :
    VIntegral' (fordZetaDetectorIntegrand eta (fordDetectorCenter t))
        (1 + eta) yLower yUpper =
      fordDetectorPhysicalResidueMass eta t yLower yUpper -
        HIntegral' (fordZetaDetectorIntegrand eta (fordDetectorCenter t))
          (1 - eta) (1 + eta) yLower +
        HIntegral' (fordZetaDetectorIntegrand eta (fordDetectorCenter t))
          (1 - eta) (1 + eta) yUpper +
        VIntegral' (fordZetaDetectorIntegrand eta (fordDetectorCenter t))
          (1 - eta) yLower yUpper := by
  have hrect :=
    fordZetaDetector_physicalRectangleIntegral_eq_explicit_sum
      heta hetaUpper ht hyLower hytLower hytUpper hboundary
  have hreLower : (fordDetectorPhysicalLower eta yLower).re = 1 - eta := by
    simp [fordDetectorPhysicalLower]
  have hreUpper : (fordDetectorPhysicalUpper eta yUpper).re = 1 + eta := by
    simp [fordDetectorPhysicalUpper]
  have himLower : (fordDetectorPhysicalLower eta yLower).im = yLower := by
    simp [fordDetectorPhysicalLower]
  have himUpper : (fordDetectorPhysicalUpper eta yUpper).im = yUpper := by
    simp [fordDetectorPhysicalUpper]
  change RectangleIntegral'
      (fordZetaDetectorIntegrand eta (fordDetectorCenter t))
      (fordDetectorPhysicalLower eta yLower)
      (fordDetectorPhysicalUpper eta yUpper) =
    fordDetectorPhysicalResidueMass eta t yLower yUpper at hrect
  simp only [RectangleIntegral', RectangleIntegral, HIntegral', VIntegral',
    smul_eq_mul] at hrect ⊢
  rw [hreLower, hreUpper, himLower, himUpper] at hrect
  linear_combination hrect

theorem re_fordDetectorPhysicalResidueMass_eq_finite_abel
    {eta t yLower yUpper : ℝ} (heta : 0 < eta) (hetaUpper : eta ≤ 1)
    (ht : 0 < t) (hyLower : yLower < 0)
    (hytLower : yLower < t) (hytUpper : t < yUpper)
    (hboundary : ∀ rho ∈ fordDetectorPhysicalZeros eta yLower yUpper,
      |rho.re - 1| < eta ∧ yLower < rho.im ∧ rho.im < yUpper)
    (hzetaLeft : ∀ u ∈ uIcc (fordDetectorPhysicalScale eta t yLower)
        (fordDetectorPhysicalScale eta t yUpper),
      riemannZeta (fordDetectorCenter t + (-eta : ℂ) +
        (2 * eta * u / Real.pi : ℝ) * I) ≠ 0)
    (hzetaTop : ∀ x : ℝ,
      riemannZeta (fordHorizontalPoint t (yUpper - t) x) ≠ 0)
    (hzetaBottom : ∀ x : ℝ,
      riemannZeta (fordHorizontalPoint t (yLower - t) x) ≠ 0) :
    (fordDetectorPhysicalResidueMass eta t yLower yUpper).re =
      fordDetectorPhysicalVerticalBulk eta t (eta : ℂ) yLower yUpper -
        fordDetectorPhysicalVerticalBulk eta t (-eta : ℂ) yLower yUpper -
        (fordDetectorHorizontalRemainder eta t (yLower - t)).re +
        (fordDetectorHorizontalRemainder eta t (yUpper - t)).re := by
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
  have hedge := fordZetaDetector_physicalRightEdge_eq_explicit_add_edges
    heta hetaUpper ht hyLower hytLower hytUpper hboundary
  have hre := congrArg Complex.re hedge
  simp only [Complex.add_re, Complex.sub_re] at hre
  rw [re_fordZetaDetector_physicalRightEdge_eq_bulk_sub_boundary heta,
    re_fordZetaDetector_physicalLeftEdge_eq_bulk_sub_boundary
      heta hzetaLeft] at hre
  have htopHeight : yUpper = t + (yUpper - t) := by ring
  rw [htopHeight,
    re_HIntegral'_fordZetaDetector_eq_boundary_sub_remainder
      heta htopOffset htop1 hzetaTop] at hre
  have hbottomHeight : yLower = t + (yLower - t) := by ring
  rw [hbottomHeight,
    re_HIntegral'_fordZetaDetector_eq_boundary_sub_remainder
      heta hbottomOffset hbottom1 hzetaBottom] at hre
  have htopRestore : t + (yUpper - t) = yUpper := by ring
  have hbottomRestore : t + (yLower - t) = yLower := by ring
  rw [htopRestore, hbottomRestore] at hre
  rw [fordDetector_scaledOffset_eq_physicalScale,
    fordDetector_scaledOffset_eq_physicalScale] at hre
  linear_combination -hre

end

end GafniTao
