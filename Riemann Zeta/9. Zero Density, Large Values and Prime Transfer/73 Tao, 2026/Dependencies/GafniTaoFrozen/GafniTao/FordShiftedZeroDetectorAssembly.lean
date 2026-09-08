import GafniTao.FordShiftedZeroDetectorHorizontalLog
import GafniTao.FordZeroDetectorAbelAssembly

/-!
# Finite Abel assembly for Ford's shifted detector

The result retains the zeta-pole contribution.  At `sigma = 1` its real part
vanishes; for `sigma > 1` it is a genuine positive correction that must be
bounded in later inequalities.
-/

open Complex Set MeasureTheory
open RiemannZeta.GuthMaynard
open scoped BigOperators

namespace GafniTao

noncomputable section

def fordShiftedDetectorResidueMass
    (sigma eta t R : ℝ) : ℂ :=
  fordDetectorZetaLogDeriv (fordShiftedDetectorCenter sigma t) -
      fordCotKernel eta (1 - fordShiftedDetectorCenter sigma t) +
    ∑ rho ∈ fordShiftedDetectorZeros sigma eta t R,
      (analyticVanishingOrder riemannZeta rho : ℂ) *
        fordCotKernel eta
          (rho - fordShiftedDetectorCenter sigma t)

theorem fordShiftedDetector_verticalPoint_top
    (sigma t side R : ℝ) :
    fordShiftedDetectorCenter sigma t + (side : ℂ) + (R : ℝ) * I =
      fordHorizontalPoint t R (sigma + side) := by
  unfold fordShiftedDetectorCenter fordHorizontalPoint
  push_cast
  ring_nf

theorem fordShiftedDetector_verticalPoint_bottom
    (sigma t side R : ℝ) :
    fordShiftedDetectorCenter sigma t + (side : ℂ) + (-R : ℝ) * I =
      fordHorizontalPoint t (-R) (sigma + side) := by
  unfold fordShiftedDetectorCenter fordHorizontalPoint
  push_cast
  ring_nf

theorem re_fordZetaShiftedDetector_rightEdge_eq_bulk_sub_boundary
    {sigma eta t R : ℝ} (hsigma : 1 ≤ sigma) (heta : 0 < eta) :
    (VIntegral'
      (fordZetaDetectorIntegrand eta
        (fordShiftedDetectorCenter sigma t))
      (sigma + eta) (t - R) (t + R)).re =
      fordShiftedDetectorVerticalBulk eta sigma t eta R -
        (Real.tanh (fordDetectorScaledHeight eta R) / (4 * eta)) *
          (fordDetectorEdgeLog t R (sigma + eta) +
            fordDetectorEdgeLog t (-R) (sigma + eta)) := by
  rw [re_fordZetaShiftedDetector_rightEdge_eq_logIntegral hsigma heta]
  have hdiv := fordDetector_height_div_scale (R := R) heta
  have hnegDiv :
      -R / (2 * eta / Real.pi) =
        -fordDetectorScaledHeight eta R := by
    rw [neg_div, hdiv]
  have hunscale := fordDetector_scaledHeight_unscale (R := R) heta
  have hnegUnscale :
      2 * eta * (-fordDetectorScaledHeight eta R) / Real.pi = -R := by
    rw [show 2 * eta * (-fordDetectorScaledHeight eta R) / Real.pi =
      -(2 * eta * fordDetectorScaledHeight eta R / Real.pi) by ring,
      hunscale]
  rw [hdiv, hnegDiv]
  change _ = fordShiftedDetectorVerticalBulk eta sigma t eta R - _
  unfold fordShiftedDetectorVerticalBulk fordDetectorEdgeLog
  rw [hunscale, hnegUnscale,
    fordShiftedDetector_verticalPoint_top,
    fordShiftedDetector_verticalPoint_bottom,
    Real.tanh_neg]
  ring

theorem re_fordZetaShiftedDetector_leftEdge_eq_bulk_sub_boundary
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
      fordShiftedDetectorVerticalBulk eta sigma t (-eta) R -
        (Real.tanh (fordDetectorScaledHeight eta R) / (4 * eta)) *
          (fordDetectorEdgeLog t R (sigma - eta) +
            fordDetectorEdgeLog t (-R) (sigma - eta)) := by
  rw [re_fordZetaShiftedDetector_leftEdge_eq_logIntegral
    heta hleftOne hzeta]
  have hdiv := fordDetector_height_div_scale (R := R) heta
  have hnegDiv :
      -R / (2 * eta / Real.pi) =
        -fordDetectorScaledHeight eta R := by
    rw [neg_div, hdiv]
  have hunscale := fordDetector_scaledHeight_unscale (R := R) heta
  have hnegUnscale :
      2 * eta * (-fordDetectorScaledHeight eta R) / Real.pi = -R := by
    rw [show 2 * eta * (-fordDetectorScaledHeight eta R) / Real.pi =
      -(2 * eta * fordDetectorScaledHeight eta R / Real.pi) by ring,
      hunscale]
  rw [hdiv, hnegDiv]
  change _ = fordShiftedDetectorVerticalBulk eta sigma t (-eta) R - _
  have hbulk :
      fordShiftedDetectorVerticalBulk eta sigma t (-eta) R =
        (1 / (4 * eta)) *
          ∫ u in (-fordDetectorScaledHeight eta R)..
              (fordDetectorScaledHeight eta R),
            Real.log ‖riemannZeta
              (fordShiftedDetectorCenter sigma t + (-eta : ℂ) +
                (2 * eta * u / Real.pi : ℝ) * I)‖ /
              Real.cosh u ^ 2 := by
    simp [fordShiftedDetectorVerticalBulk]
  rw [hbulk]
  unfold fordDetectorEdgeLog
  have htop :
      fordShiftedDetectorCenter sigma t + -(eta : ℂ) + (R : ℝ) * I =
        fordHorizontalPoint t R (sigma - eta) := by
    unfold fordShiftedDetectorCenter fordHorizontalPoint
    push_cast
    ring
  have hbottom :
      fordShiftedDetectorCenter sigma t + -(eta : ℂ) + (-R : ℝ) * I =
        fordHorizontalPoint t (-R) (sigma - eta) := by
    unfold fordShiftedDetectorCenter fordHorizontalPoint
    push_cast
    ring
  rw [hunscale, hnegUnscale, htop, hbottom, Real.tanh_neg]
  ring

theorem re_HIntegral'_fordZetaShiftedDetector_eq_boundary_sub_remainder
    {sigma eta t y : ℝ} (heta : 0 < eta) (hy : y ≠ 0)
    (h1 : ∀ x : ℝ, fordHorizontalPoint t y x ≠ 1)
    (hzeta : ∀ x : ℝ,
      riemannZeta (fordHorizontalPoint t y x) ≠ 0) :
    (HIntegral'
      (fordZetaDetectorIntegrand eta
        (fordShiftedDetectorCenter sigma t))
      (sigma - eta) (sigma + eta) (t + y)).re =
      (-Real.tanh (fordDetectorScaledHeight eta y) / (4 * eta)) *
          (fordDetectorEdgeLog t y (sigma + eta) -
            fordDetectorEdgeLog t y (sigma - eta)) -
        (fordShiftedHorizontalRemainder sigma eta t y).re := by
  rw [HIntegral'_fordZetaShiftedDetector_eq_boundary_sub
    heta hy h1 hzeta]
  simp only [Complex.sub_re]
  rw [re_fordShiftedHorizontal_boundary_eq heta h1 hzeta]
  rfl

theorem fordZetaShiftedDetector_rightEdge_eq_explicit_add_edges
    {sigma eta t R : ℝ} (hsigma : 1 ≤ sigma) (heta : 0 < eta)
    (ht : 0 < t) (hPole : sigma - 1 < eta) (hR : |t| < R)
    (hleft : -1 ≤ sigma - eta)
    (hboundary : ∀ rho ∈ fordShiftedDetectorZeros sigma eta t R,
      |rho.re - sigma| < eta ∧ |rho.im - t| < R) :
    VIntegral'
      (fordZetaDetectorIntegrand eta
        (fordShiftedDetectorCenter sigma t))
      (sigma + eta) (t - R) (t + R) =
      fordShiftedDetectorResidueMass sigma eta t R -
        HIntegral'
          (fordZetaDetectorIntegrand eta
            (fordShiftedDetectorCenter sigma t))
          (sigma - eta) (sigma + eta) (t - R) +
        HIntegral'
          (fordZetaDetectorIntegrand eta
            (fordShiftedDetectorCenter sigma t))
          (sigma - eta) (sigma + eta) (t + R) +
        VIntegral'
          (fordZetaDetectorIntegrand eta
            (fordShiftedDetectorCenter sigma t))
          (sigma - eta) (t - R) (t + R) := by
  have hrect :=
    fordZetaShiftedDetector_rectangleIntegral_eq_explicit_sum
      hsigma heta ht hPole hR hleft hboundary
  have hreLower :
      (fordShiftedDetectorLower sigma eta t R).re = sigma - eta := by
    simp [fordShiftedDetectorLower]
  have hreUpper :
      (fordShiftedDetectorUpper sigma eta t R).re = sigma + eta := by
    simp [fordShiftedDetectorUpper]
  have himLower :
      (fordShiftedDetectorLower sigma eta t R).im = t - R := by
    simp [fordShiftedDetectorLower]
  have himUpper :
      (fordShiftedDetectorUpper sigma eta t R).im = t + R := by
    simp [fordShiftedDetectorUpper]
  change RectangleIntegral'
      (fordZetaDetectorIntegrand eta
        (fordShiftedDetectorCenter sigma t))
      (fordShiftedDetectorLower sigma eta t R)
      (fordShiftedDetectorUpper sigma eta t R) =
    fordShiftedDetectorResidueMass sigma eta t R at hrect
  simp only [RectangleIntegral', RectangleIntegral, HIntegral', VIntegral',
    smul_eq_mul] at hrect ⊢
  rw [hreLower, hreUpper, himLower, himUpper] at hrect
  linear_combination hrect

/-- Exact finite shifted Abel formula, including the zeta-pole term in the
residue mass. -/
theorem re_fordShiftedDetectorResidueMass_eq_finite_abel
    {sigma eta t R : ℝ} (hsigma : 1 ≤ sigma) (heta : 0 < eta)
    (ht : 0 < t) (hPole : sigma - 1 < eta) (hR : |t| < R)
    (hleft : -1 ≤ sigma - eta) (hleftOne : sigma - eta ≠ 1)
    (hboundary : ∀ rho ∈ fordShiftedDetectorZeros sigma eta t R,
      |rho.re - sigma| < eta ∧ |rho.im - t| < R)
    (hzetaLeft : ∀ u ∈ uIcc (-R / (2 * eta / Real.pi))
        (R / (2 * eta / Real.pi)),
      riemannZeta
        (fordShiftedDetectorCenter sigma t + (-eta : ℂ) +
          (2 * eta * u / Real.pi : ℝ) * I) ≠ 0)
    (hzetaTop : ∀ x : ℝ,
      riemannZeta (fordHorizontalPoint t R x) ≠ 0)
    (hzetaBottom : ∀ x : ℝ,
      riemannZeta (fordHorizontalPoint t (-R) x) ≠ 0) :
    (fordShiftedDetectorResidueMass sigma eta t R).re =
      fordShiftedDetectorVerticalBulk eta sigma t eta R -
        fordShiftedDetectorVerticalBulk eta sigma t (-eta) R -
        (fordShiftedHorizontalRemainder sigma eta t (-R)).re +
        (fordShiftedHorizontalRemainder sigma eta t R).re := by
  have hRpos : 0 < R := (abs_nonneg t).trans_lt hR
  have htopIm : t + R ≠ 0 := by positivity
  have hbottomIm : t + -R ≠ 0 := by
    intro heq
    have : t = R := by linarith
    rw [this, abs_of_pos hRpos] at hR
    exact (lt_irrefl R hR)
  have htop1 : ∀ x : ℝ, fordHorizontalPoint t R x ≠ 1 :=
    fun _x => fordHorizontalPoint_ne_one_of_im_ne_zero htopIm
  have hbottom1 : ∀ x : ℝ,
      fordHorizontalPoint t (-R) x ≠ 1 :=
    fun _x => fordHorizontalPoint_ne_one_of_im_ne_zero hbottomIm
  have hedge := fordZetaShiftedDetector_rightEdge_eq_explicit_add_edges
    hsigma heta ht hPole hR hleft hboundary
  have hre := congrArg Complex.re hedge
  simp only [Complex.add_re, Complex.sub_re] at hre
  rw [re_fordZetaShiftedDetector_rightEdge_eq_bulk_sub_boundary
      hsigma heta,
    re_fordZetaShiftedDetector_leftEdge_eq_bulk_sub_boundary
      heta hleftOne hzetaLeft,
    re_HIntegral'_fordZetaShiftedDetector_eq_boundary_sub_remainder
      heta hRpos.ne' htop1 hzetaTop] at hre
  have htm : t - R = t + -R := by ring
  rw [htm,
    re_HIntegral'_fordZetaShiftedDetector_eq_boundary_sub_remainder
      heta (neg_ne_zero.mpr hRpos.ne') hbottom1 hzetaBottom] at hre
  have hscaledNeg :
      fordDetectorScaledHeight eta (-R) =
        -fordDetectorScaledHeight eta R := by
    unfold fordDetectorScaledHeight
    ring
  rw [hscaledNeg, Real.tanh_neg] at hre
  linear_combination -hre

end

end GafniTao
