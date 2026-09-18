import Tao2026.SmoothNumberSaddleHTShiftedZeroFree

/-!
# Source contour parameters for the HT Mangoldt estimate

This module fixes the shifted-Perron rectangle used at the full HT frequency
ceiling.  Its left displacement is `2*(log y)^(ε/2-1)`, so the left-edge
power has one full extra copy of the requested source saving; this absorbs
the logarithmic losses on the displaced edges.  Its height is twice the
frequency ceiling, and its initial right line is `β + 1/log y`.

The final theorem combines the right-line Dirichlet-series identity with the
zero-free contour displacement.  It reduces the HT transform error exactly
to two named analytic remainders: the three displaced contour edges and the
finite-height Perron truncation error.
-/

open Filter Topology MeasureTheory Set Complex Finset
open scoped ArithmeticFunction.vonMangoldt BigOperators Interval

namespace Tao2026

noncomputable section

noncomputable def smoothSaddleHTContourShift (y : ℕ) (ε : ℝ) : ℝ :=
  2 * (Real.log y) ^ (ε / 2 - 1)

noncomputable def smoothSaddleHTContourHeight (y : ℕ) (ε : ℝ) : ℝ :=
  2 * smoothSaddleHTFrequencyCeiling y ε

noncomputable def smoothSaddleHTContourRight (y : ℕ) (β : ℝ) : ℝ :=
  β + 1 / Real.log y

theorem smoothSaddleHTContourShift_pos {y : ℕ} (hy : 2 ≤ y) (ε : ℝ) :
    0 < smoothSaddleHTContourShift y ε := by
  unfold smoothSaddleHTContourShift
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  exact mul_pos (by norm_num) (Real.rpow_pos_of_pos hlog _)

theorem smoothSaddleHTContourRight_sub (y : ℕ) (β : ℝ) :
    smoothSaddleHTContourRight y β - β = 1 / Real.log y := by
  unfold smoothSaddleHTContourRight
  ring

theorem smoothSaddleHTSourceExponent_re_add_contourRight
    (y : ℕ) (β : ℝ) :
    (1 - β) + smoothSaddleHTContourRight y β = 1 + 1 / Real.log y := by
  unfold smoothSaddleHTContourRight
  ring

theorem smoothSaddleHTContourRight_gt {y : ℕ} (hy : 2 ≤ y) (β : ℝ) :
    β < smoothSaddleHTContourRight y β := by
  rw [show smoothSaddleHTContourRight y β = β + 1 / Real.log y by rfl]
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  exact lt_add_of_pos_right β (one_div_pos.mpr hlog)

theorem rpow_smoothSaddleHTContourRight {y : ℕ} (hy : 2 ≤ y) (β : ℝ) :
    (y : ℝ) ^ smoothSaddleHTContourRight y β =
      (y : ℝ) ^ β * Real.exp 1 := by
  have hypos : 0 < (y : ℝ) := by positivity
  have hlog : Real.log (y : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < y by omega)))
  have hunit : (y : ℝ) ^ (1 / Real.log y) = Real.exp 1 := by
    rw [Real.rpow_def_of_pos hypos]
    congr 1
    field_simp
  unfold smoothSaddleHTContourRight
  rw [Real.rpow_add hypos, hunit]

theorem smoothSaddleHTContourHeight_pos (y : ℕ) (ε : ℝ) :
    0 < smoothSaddleHTContourHeight y ε := by
  unfold smoothSaddleHTContourHeight
  exact mul_pos (by norm_num) (smoothSaddleHTFrequencyCeiling_pos y ε)

theorem smoothSaddleHTFrequencyCeiling_lt_contourHeight (y : ℕ) (ε : ℝ) :
    smoothSaddleHTFrequencyCeiling y ε < smoothSaddleHTContourHeight y ε := by
  unfold smoothSaddleHTContourHeight
  have h := smoothSaddleHTFrequencyCeiling_pos y ε
  linarith

theorem smoothSaddleHT_totalHeight_le {y : ℕ} {ε t : ℝ}
    (ht : |t| ≤ smoothSaddleHTFrequencyCeiling y ε) :
    |t| + smoothSaddleHTContourHeight y ε ≤
      3 * smoothSaddleHTFrequencyCeiling y ε := by
  unfold smoothSaddleHTContourHeight
  linarith

theorem smoothSaddleHTContourShift_mul_log
    {y : ℕ} (hy : 2 ≤ y) (ε : ℝ) :
    smoothSaddleHTContourShift y ε * Real.log y =
      2 * (Real.log y) ^ (ε / 2) := by
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  unfold smoothSaddleHTContourShift
  calc
    2 * (Real.log y) ^ (ε / 2 - 1) * Real.log y =
        2 * ((Real.log y) ^ (ε / 2 - 1) *
          (Real.log y) ^ (1 : ℝ)) := by
          rw [Real.rpow_one]
          ring
    _ = 2 * (Real.log y) ^ ((ε / 2 - 1) + 1) := by
          rw [← Real.rpow_add hlog]
    _ = 2 * (Real.log y) ^ (ε / 2) := by ring_nf

theorem rpow_neg_smoothSaddleHTContourShift
    {y : ℕ} (hy : 2 ≤ y) (ε : ℝ) :
    (y : ℝ) ^ (-smoothSaddleHTContourShift y ε) =
      Real.exp (-2 * (Real.log y) ^ (ε / 2)) := by
  have hypos : 0 < (y : ℝ) := by positivity
  rw [Real.rpow_def_of_pos hypos]
  congr 1
  rw [show Real.log y * -smoothSaddleHTContourShift y ε =
      -(smoothSaddleHTContourShift y ε * Real.log y) by ring,
    smoothSaddleHTContourShift_mul_log hy ε]
  ring

noncomputable def smoothSaddleHTContourEdgeContribution
    (y : ℕ) (beta ε t : ℝ) : ℂ :=
  -HIntegral'
      (smoothSaddleHTShiftedZetaPerronIntegrand (y : ℝ)
        (smoothSaddleHTSourceExponent beta t))
      (beta - smoothSaddleHTContourShift y ε)
      (smoothSaddleHTContourRight y beta)
      (-smoothSaddleHTContourHeight y ε) +
    HIntegral'
      (smoothSaddleHTShiftedZetaPerronIntegrand (y : ℝ)
        (smoothSaddleHTSourceExponent beta t))
      (beta - smoothSaddleHTContourShift y ε)
      (smoothSaddleHTContourRight y beta)
      (smoothSaddleHTContourHeight y ε) +
    VIntegral'
      (smoothSaddleHTShiftedZetaPerronIntegrand (y : ℝ)
        (smoothSaddleHTSourceExponent beta t))
      (beta - smoothSaddleHTContourShift y ε)
      (-smoothSaddleHTContourHeight y ε)
      (smoothSaddleHTContourHeight y ε)

noncomputable def smoothSaddleHTContourTruncationError
    (y : ℕ) (beta ε t : ℝ) : ℂ :=
  ∑' n : ℕ,
    smoothSaddleHTShiftedMangoldtCoefficient
        (smoothSaddleHTSourceExponent beta t) n *
      (GafniTao.sharpPerronKernel
          (smoothSaddleHTContourRight y beta)
          (smoothSaddleHTContourHeight y ε) (y : ℝ) n -
        GafniTao.sharpPerronCutoff (y : ℝ) n)

theorem smoothSaddleHTMangoldtTransform_sub_mainTerm_eq_contourErrors
    {c H beta ε t : ℝ} {y : ℕ}
    (hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H)
    (hy : 2 ≤ y)
    (hbetaShift : smoothSaddleHTContourShift y ε < beta)
    (hshiftOne : smoothSaddleHTContourShift y ε ≤ 1)
    (ht : |t| ≤ smoothSaddleHTFrequencyCeiling y ε)
    (hHeight : H ≤ |t| + smoothSaddleHTContourHeight y ε)
    (hWidth : smoothSaddleHTContourShift y ε ≤ c /
      GafniTao.vinogradovKorobovDenominator
        (|t| + smoothSaddleHTContourHeight y ε)) :
    smoothSaddleHTMangoldtTransform y beta t -
        smoothSaddleHTMangoldtMainTerm y beta t =
      smoothSaddleHTContourEdgeContribution y beta ε t -
        smoothSaddleHTContourTruncationError y beta ε t := by
  have hyPos : 0 < y := by omega
  have hshiftPos := smoothSaddleHTContourShift_pos hy ε
  have hright := smoothSaddleHTContourRight_gt hy beta
  have htStrict : |t| < smoothSaddleHTContourHeight y ε :=
    ht.trans_lt (smoothSaddleHTFrequencyCeiling_lt_contourHeight y ε)
  have hrect :=
    smoothSaddleHTSource_shiftedPerron_rightLine_eq_main_add_edges_of_vK
      (c := c) (H := H)
      (eta := smoothSaddleHTContourShift y ε)
      (beta := beta) (t := t)
      (T := smoothSaddleHTContourHeight y ε)
      (right := smoothSaddleHTContourRight y beta)
      (y := y) hZeroFree hyPos hshiftPos hbetaShift hshiftOne hright
      htStrict hHeight hWidth
  have herr := smoothSaddleHTSource_shiftedPerron_error_identity
    (c := smoothSaddleHTContourRight y beta)
    (T := smoothSaddleHTContourHeight y ε)
    (y := y) (beta := beta) (t := t)
    hright (lt_trans (lt_trans hshiftPos hbetaShift) hright)
      (by omega : 1 ≤ y)
  rw [smoothSaddleHTMangoldtMainTerm_eq_sourceMainTerm hyPos beta t]
  unfold smoothSaddleHTContourEdgeContribution
    smoothSaddleHTContourTruncationError
  linear_combination hrect - herr

theorem norm_smoothSaddleHTMangoldtTransform_sub_mainTerm_le_contourErrors
    {c H beta ε t : ℝ} {y : ℕ}
    (hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H)
    (hy : 2 ≤ y)
    (hbetaShift : smoothSaddleHTContourShift y ε < beta)
    (hshiftOne : smoothSaddleHTContourShift y ε ≤ 1)
    (ht : |t| ≤ smoothSaddleHTFrequencyCeiling y ε)
    (hHeight : H ≤ |t| + smoothSaddleHTContourHeight y ε)
    (hWidth : smoothSaddleHTContourShift y ε ≤ c /
      GafniTao.vinogradovKorobovDenominator
        (|t| + smoothSaddleHTContourHeight y ε)) :
    ‖smoothSaddleHTMangoldtTransform y beta t -
        smoothSaddleHTMangoldtMainTerm y beta t‖ ≤
      ‖smoothSaddleHTContourEdgeContribution y beta ε t‖ +
        ‖smoothSaddleHTContourTruncationError y beta ε t‖ := by
  rw [smoothSaddleHTMangoldtTransform_sub_mainTerm_eq_contourErrors
    hZeroFree hy hbetaShift hshiftOne ht hHeight hWidth]
  exact norm_sub_le _ _

end

end Tao2026
