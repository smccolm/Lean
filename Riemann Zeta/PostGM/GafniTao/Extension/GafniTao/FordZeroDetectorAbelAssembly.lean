import GafniTao.FordZeroDetectorHorizontalLog

/-!
# Finite Abel assembly for Ford's zero detector

The vertical and horizontal integration-by-parts identities are assembled
here.  All four endpoint contributions cancel algebraically.  The resulting
finite formula retains exactly the two horizontal derivative integrals which
must be sent to zero along Ford's good heights.
-/

open Complex Set MeasureTheory
open RiemannZeta.GuthMaynard
open scoped BigOperators

namespace GafniTao

noncomputable section

def fordDetectorScaledHeight (eta R : ℝ) : ℝ :=
  Real.pi * R / (2 * eta)

def fordDetectorEdgeLog (t y x : ℝ) : ℝ :=
  Real.log ‖riemannZeta (fordHorizontalPoint t y x)‖

def fordDetectorVerticalBulk
    (eta t : ℝ) (side : ℂ) (R : ℝ) : ℝ :=
  (1 / (4 * eta)) *
    ∫ u in (-fordDetectorScaledHeight eta R)..
        (fordDetectorScaledHeight eta R),
      Real.log ‖riemannZeta
        (fordDetectorCenter t + side +
          (2 * eta * u / Real.pi : ℝ) * I)‖ /
        Real.cosh u ^ 2

def fordDetectorHorizontalRemainder
    (eta t y : ℝ) : ℂ :=
  ∫ x in (1 - eta)..(1 + eta),
    fordHorizontalWeightDeriv eta y x *
      fordHorizontalNormalizedLogLift t y (1 - eta) x

def fordDetectorResidueMass (eta t R : ℝ) : ℂ :=
  fordDetectorZetaLogDeriv (fordDetectorCenter t) -
      fordCotKernel eta (1 - fordDetectorCenter t) +
    ∑ rho ∈ fordDetectorZeros eta t R,
      (analyticVanishingOrder riemannZeta rho : ℂ) *
        fordCotKernel eta (rho - fordDetectorCenter t)

theorem fordDetector_height_div_scale
    {eta R : ℝ} (heta : 0 < eta) :
    R / (2 * eta / Real.pi) = fordDetectorScaledHeight eta R := by
  unfold fordDetectorScaledHeight
  field_simp [heta.ne', Real.pi_ne_zero]

theorem fordDetector_scaledHeight_unscale
    {eta R : ℝ} (heta : 0 < eta) :
    2 * eta * fordDetectorScaledHeight eta R / Real.pi = R := by
  unfold fordDetectorScaledHeight
  field_simp [heta.ne', Real.pi_ne_zero]

theorem fordDetector_verticalPoint_top
    (t side R : ℝ) :
    fordDetectorCenter t + (side : ℂ) + (R : ℝ) * I =
      fordHorizontalPoint t R (1 + side) := by
  unfold fordDetectorCenter fordHorizontalPoint
  push_cast
  ring

theorem fordDetector_verticalPoint_bottom
    (t side R : ℝ) :
    fordDetectorCenter t + (side : ℂ) + (-R : ℝ) * I =
      fordHorizontalPoint t (-R) (1 + side) := by
  unfold fordDetectorCenter fordHorizontalPoint
  push_cast
  ring

theorem fordHorizontalPoint_ne_one_of_im_ne_zero
    {t y x : ℝ} (him : t + y ≠ 0) :
    fordHorizontalPoint t y x ≠ 1 := by
  intro heq
  have hi := congrArg Complex.im heq
  simp [fordHorizontalPoint] at hi
  exact him hi

theorem re_fordZetaDetector_rightEdge_eq_bulk_sub_boundary
    {eta t R : ℝ} (heta : 0 < eta) :
    (VIntegral' (fordZetaDetectorIntegrand eta (fordDetectorCenter t))
        (1 + eta) (t - R) (t + R)).re =
      fordDetectorVerticalBulk eta t (eta : ℂ) R -
        (Real.tanh (fordDetectorScaledHeight eta R) / (4 * eta)) *
          (fordDetectorEdgeLog t R (1 + eta) +
            fordDetectorEdgeLog t (-R) (1 + eta)) := by
  rw [re_fordZetaDetector_rightEdge_eq_logIntegral heta]
  have hdiv := fordDetector_height_div_scale (R := R) heta
  have hnegDiv :
      -R / (2 * eta / Real.pi) = -fordDetectorScaledHeight eta R := by
    rw [neg_div, hdiv]
  have hunscale := fordDetector_scaledHeight_unscale (R := R) heta
  have hnegUnscale :
      2 * eta * (-fordDetectorScaledHeight eta R) / Real.pi = -R := by
    rw [show 2 * eta * (-fordDetectorScaledHeight eta R) / Real.pi =
      -(2 * eta * fordDetectorScaledHeight eta R / Real.pi) by ring,
      hunscale]
  rw [hdiv, hnegDiv]
  change _ = fordDetectorVerticalBulk eta t (eta : ℂ) R - _
  unfold fordDetectorVerticalBulk fordDetectorEdgeLog
  rw [hunscale, hnegUnscale,
    fordDetector_verticalPoint_top,
    fordDetector_verticalPoint_bottom,
    Real.tanh_neg]
  ring

theorem re_fordZetaDetector_leftEdge_eq_bulk_sub_boundary
    {eta t R : ℝ} (heta : 0 < eta)
    (hzeta : ∀ u ∈ uIcc (-R / (2 * eta / Real.pi))
        (R / (2 * eta / Real.pi)),
      riemannZeta (fordDetectorCenter t + (-eta : ℂ) +
        (2 * eta * u / Real.pi : ℝ) * I) ≠ 0) :
    (VIntegral' (fordZetaDetectorIntegrand eta (fordDetectorCenter t))
        (1 - eta) (t - R) (t + R)).re =
      fordDetectorVerticalBulk eta t (-eta : ℂ) R -
        (Real.tanh (fordDetectorScaledHeight eta R) / (4 * eta)) *
          (fordDetectorEdgeLog t R (1 - eta) +
            fordDetectorEdgeLog t (-R) (1 - eta)) := by
  rw [re_fordZetaDetector_leftEdge_eq_logIntegral heta hzeta]
  have hdiv := fordDetector_height_div_scale (R := R) heta
  have hnegDiv :
      -R / (2 * eta / Real.pi) = -fordDetectorScaledHeight eta R := by
    rw [neg_div, hdiv]
  have hunscale := fordDetector_scaledHeight_unscale (R := R) heta
  have hnegUnscale :
      2 * eta * (-fordDetectorScaledHeight eta R) / Real.pi = -R := by
    rw [show 2 * eta * (-fordDetectorScaledHeight eta R) / Real.pi =
      -(2 * eta * fordDetectorScaledHeight eta R / Real.pi) by ring,
      hunscale]
  rw [hdiv, hnegDiv]
  change _ = fordDetectorVerticalBulk eta t (-eta : ℂ) R - _
  unfold fordDetectorVerticalBulk fordDetectorEdgeLog
  have htop :
      fordDetectorCenter t + -(eta : ℂ) + (R : ℝ) * I =
        fordHorizontalPoint t R (1 - eta) := by
    unfold fordDetectorCenter fordHorizontalPoint
    push_cast
    ring
  have hbottom :
      fordDetectorCenter t + -(eta : ℂ) + (-R : ℝ) * I =
        fordHorizontalPoint t (-R) (1 - eta) := by
    unfold fordDetectorCenter fordHorizontalPoint
    push_cast
    ring
  rw [hunscale, hnegUnscale,
    htop, hbottom,
    Real.tanh_neg]
  ring

theorem re_HIntegral'_fordZetaDetector_eq_boundary_sub_remainder
    {eta t y : ℝ} (heta : 0 < eta) (hy : y ≠ 0)
    (h1 : ∀ x : ℝ, fordHorizontalPoint t y x ≠ 1)
    (hzeta : ∀ x : ℝ,
      riemannZeta (fordHorizontalPoint t y x) ≠ 0) :
    (HIntegral' (fordZetaDetectorIntegrand eta (fordDetectorCenter t))
        (1 - eta) (1 + eta) (t + y)).re =
      (-Real.tanh (fordDetectorScaledHeight eta y) / (4 * eta)) *
          (fordDetectorEdgeLog t y (1 + eta) -
            fordDetectorEdgeLog t y (1 - eta)) -
        (fordDetectorHorizontalRemainder eta t y).re := by
  rw [HIntegral'_fordZetaDetector_eq_boundary_sub
    heta hy h1 hzeta]
  simp only [Complex.sub_re]
  rw [re_fordHorizontal_boundary_eq heta h1 hzeta]
  rfl

/-- Ford's exact finite-height detector identity after integration by parts.
All four endpoint terms have cancelled; only the two horizontal derivative
remainders survive. -/
theorem re_fordDetectorResidueMass_eq_finite_abel
    {eta t R : ℝ} (heta : 0 < eta) (hetaUpper : eta ≤ 1)
    (ht : 0 < t) (hR : |t| < R)
    (hboundary : ∀ rho ∈ fordDetectorZeros eta t R,
      |rho.re - 1| < eta ∧ |rho.im - t| < R)
    (hzetaLeft : ∀ u ∈ uIcc (-R / (2 * eta / Real.pi))
        (R / (2 * eta / Real.pi)),
      riemannZeta (fordDetectorCenter t + (-eta : ℂ) +
        (2 * eta * u / Real.pi : ℝ) * I) ≠ 0)
    (hzetaTop : ∀ x : ℝ,
      riemannZeta (fordHorizontalPoint t R x) ≠ 0)
    (hzetaBottom : ∀ x : ℝ,
      riemannZeta (fordHorizontalPoint t (-R) x) ≠ 0) :
    (fordDetectorResidueMass eta t R).re =
      fordDetectorVerticalBulk eta t (eta : ℂ) R -
        fordDetectorVerticalBulk eta t (-eta : ℂ) R -
        (fordDetectorHorizontalRemainder eta t (-R)).re +
        (fordDetectorHorizontalRemainder eta t R).re := by
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
  have hedge := fordZetaDetector_rightEdge_eq_explicit_add_edges
    heta hetaUpper ht hR hboundary
  change
    VIntegral' (fordZetaDetectorIntegrand eta (fordDetectorCenter t))
        (1 + eta) (t - R) (t + R) =
      fordDetectorResidueMass eta t R -
        HIntegral' (fordZetaDetectorIntegrand eta (fordDetectorCenter t))
          (1 - eta) (1 + eta) (t - R) +
        HIntegral' (fordZetaDetectorIntegrand eta (fordDetectorCenter t))
          (1 - eta) (1 + eta) (t + R) +
        VIntegral' (fordZetaDetectorIntegrand eta (fordDetectorCenter t))
          (1 - eta) (t - R) (t + R) at hedge
  have hre := congrArg Complex.re hedge
  simp only [Complex.add_re, Complex.sub_re] at hre
  rw [re_fordZetaDetector_rightEdge_eq_bulk_sub_boundary heta,
    re_fordZetaDetector_leftEdge_eq_bulk_sub_boundary heta hzetaLeft,
    re_HIntegral'_fordZetaDetector_eq_boundary_sub_remainder
      heta hRpos.ne' htop1 hzetaTop] at hre
  have htm : t - R = t + -R := by ring
  rw [htm,
    re_HIntegral'_fordZetaDetector_eq_boundary_sub_remainder
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
