import Tao2026.SmoothNumberSaddleHTSmallBetaScale
import GafniTao.PintzZetaWindow
import GafniTao.FordShiftedRightBulkBound
import GafniTao.StrongPNTPrefix

/-!
# A zero-free variable disk for the HT small-beta branch

The physical disk has centre `1 + w + it` and radius `2w`.  If `w` is at
most the Vinogradov--Korobov width at height `|t| + T`, the whole disk lies
in the zero-free region.  In the HT small-beta branch the source point
`1 - beta + it` has normalized coordinate of norm at most `5/6`.

This is the geometric and analytic input for applying the frozen
`GafniTao.FinalBound` theorem at the native VK scale.
-/

open Complex Set Metric

namespace Tao2026

noncomputable section

/-- Centre of the physical variable disk. -/
noncomputable def smoothSaddleHTVariableDiskCenter (w t : ℝ) : ℂ :=
  ((1 + w : ℝ) : ℂ) + (t : ℂ) * Complex.I

/-- Affine map from the normalized unit disk to the physical disk of radius
`2w`. -/
noncomputable def smoothSaddleHTVariableDiskMap (w t : ℝ) (z : ℂ) : ℂ :=
  smoothSaddleHTVariableDiskCenter w t + ((2 * w : ℝ) : ℂ) * z

/-- Zeta normalized to take the value one at the centre of the disk. -/
noncomputable def smoothSaddleHTVariableDiskNormalized
    (w t : ℝ) (z : ℂ) : ℂ :=
  (riemannZeta (smoothSaddleHTVariableDiskCenter w t))⁻¹ *
    riemannZeta (smoothSaddleHTVariableDiskMap w t z)

/-- Normalized coordinate of the physical source point `1-beta+it`. -/
noncomputable def smoothSaddleHTVariableDiskSourceCoord
    (w beta : ℝ) : ℂ :=
  ((-(w + beta) / (2 * w) : ℝ) : ℂ)

@[simp] theorem smoothSaddleHTVariableDiskCenter_re (w t : ℝ) :
    (smoothSaddleHTVariableDiskCenter w t).re = 1 + w := by
  simp [smoothSaddleHTVariableDiskCenter]

@[simp] theorem smoothSaddleHTVariableDiskCenter_im (w t : ℝ) :
    (smoothSaddleHTVariableDiskCenter w t).im = t := by
  simp [smoothSaddleHTVariableDiskCenter]

@[simp] theorem smoothSaddleHTVariableDiskMap_zero (w t : ℝ) :
    smoothSaddleHTVariableDiskMap w t 0 =
      smoothSaddleHTVariableDiskCenter w t := by
  simp [smoothSaddleHTVariableDiskMap]

/-- The distinguished normalized coordinate maps exactly to the HT source
exponent. -/
theorem smoothSaddleHTVariableDiskMap_sourceCoord
    {w beta t : ℝ} (hw : 0 < w) :
    smoothSaddleHTVariableDiskMap w t
        (smoothSaddleHTVariableDiskSourceCoord w beta) =
      smoothSaddleHTSourceExponent beta t := by
  have hw0 : (2 * w : ℝ) ≠ 0 := by positivity
  have hscale : (2 * w) * (-(w + beta) / (2 * w)) = -(w + beta) := by
    field_simp
  have hscaleC :
      (((2 * w : ℝ) : ℂ) * (((-(w + beta) / (2 * w) : ℝ) : ℂ))) =
        ((-(w + beta) : ℝ) : ℂ) := by
    exact_mod_cast hscale
  rw [smoothSaddleHTVariableDiskMap,
    smoothSaddleHTVariableDiskSourceCoord, hscaleC]
  apply Complex.ext
  · simp [smoothSaddleHTVariableDiskCenter, smoothSaddleHTSourceExponent]
    ring
  · simp [smoothSaddleHTVariableDiskCenter, smoothSaddleHTSourceExponent]

/-- In the small-beta range `beta <= 2w/3`, the source coordinate lies in
the fixed normalized disk of radius `5/6`. -/
theorem norm_smoothSaddleHTVariableDiskSourceCoord_le
    {w beta : ℝ} (hw : 0 < w) (hbeta : 0 ≤ beta)
    (hbetaUpper : beta ≤ 2 * w / 3) :
    ‖smoothSaddleHTVariableDiskSourceCoord w beta‖ ≤ 5 / 6 := by
  rw [smoothSaddleHTVariableDiskSourceCoord, Complex.norm_real,
    Real.norm_eq_abs]
  have hsum : 0 ≤ w + beta := by linarith
  rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hsum)
    (by positivity : 0 ≤ 2 * w))]
  rw [neg_div, neg_neg]
  rw [div_le_iff₀ (by positivity : 0 < 2 * w)]
  nlinarith

/-- The affine image of the unit disk has real part at least `1-w`. -/
theorem smoothSaddleHTVariableDiskMap_re_lower
    {w t : ℝ} {z : ℂ} (hw : 0 ≤ w) (hz : ‖z‖ ≤ 1) :
    1 - w ≤ (smoothSaddleHTVariableDiskMap w t z).re := by
  have hzabs : |z.re| ≤ 1 := (Complex.abs_re_le_norm z).trans hz
  have hzre : -1 ≤ z.re := (abs_le.mp hzabs).1
  simp only [smoothSaddleHTVariableDiskMap,
    smoothSaddleHTVariableDiskCenter, add_re, ofReal_re, mul_re,
    ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero]
  nlinarith

/-- The affine image of the unit disk has real part at most `1+3w`. -/
theorem smoothSaddleHTVariableDiskMap_re_upper
    {w t : ℝ} {z : ℂ} (hw : 0 ≤ w) (hz : ‖z‖ ≤ 1) :
    (smoothSaddleHTVariableDiskMap w t z).re ≤ 1 + 3 * w := by
  have hzabs : |z.re| ≤ 1 := (Complex.abs_re_le_norm z).trans hz
  have hzre : z.re ≤ 1 := (abs_le.mp hzabs).2
  simp only [smoothSaddleHTVariableDiskMap,
    smoothSaddleHTVariableDiskCenter, add_re, ofReal_re, mul_re,
    ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero]
  nlinarith

/-- The affine image changes the imaginary part by at most `2w`. -/
theorem abs_smoothSaddleHTVariableDiskMap_im_sub_le
    {w t : ℝ} {z : ℂ} (hw : 0 ≤ w) (hz : ‖z‖ ≤ 1) :
    |(smoothSaddleHTVariableDiskMap w t z).im - t| ≤ 2 * w := by
  have hzim : |z.im| ≤ 1 := (Complex.abs_im_le_norm z).trans hz
  simp only [smoothSaddleHTVariableDiskMap,
    smoothSaddleHTVariableDiskCenter, add_im, ofReal_im, mul_im,
    ofReal_re, I_im, I_re, zero_mul, mul_one, add_zero]
  rw [show 0 + t + 2 * w * z.im - t = 2 * w * z.im by ring,
    abs_mul]
  simp only [abs_of_nonneg (by positivity : 0 ≤ 2 * w)]
  exact mul_le_of_le_one_right (by positivity) hzim

/-- The physical disk stays inside the enclosing height `|t|+T` whenever
its radius is at most `T`. -/
theorem abs_smoothSaddleHTVariableDiskMap_im_le_totalHeight
    {w t T : ℝ} {z : ℂ} (hw : 0 ≤ w) (hz : ‖z‖ ≤ 1)
    (hRadius : 2 * w ≤ T) :
    |(smoothSaddleHTVariableDiskMap w t z).im| ≤ |t| + T := by
  have hdiff := abs_smoothSaddleHTVariableDiskMap_im_sub_le
    (t := t) hw hz
  calc
    |(smoothSaddleHTVariableDiskMap w t z).im| =
        |t + ((smoothSaddleHTVariableDiskMap w t z).im - t)| := by
      congr 1
      ring
    _ ≤
        |t| + |(smoothSaddleHTVariableDiskMap w t z).im - t| := by
      exact abs_add_le _ _
    _ ≤ |t| + T := by
      simpa [add_comm] using add_le_add_left (hdiff.trans hRadius) |t|

/-- At high height the physical disk avoids the zeta pole. -/
theorem smoothSaddleHTVariableDiskMap_ne_one
    {w t : ℝ} {z : ℂ} (hw : 0 ≤ w) (hz : ‖z‖ ≤ 1)
    (hwOne : w ≤ 1) (ht : 3 < |t|) :
    smoothSaddleHTVariableDiskMap w t z ≠ 1 := by
  intro heq
  have him := congrArg Complex.im heq
  have hdiff := abs_smoothSaddleHTVariableDiskMap_im_sub_le
    (t := t) hw hz
  rw [him] at hdiff
  simp only [Complex.one_im, zero_sub, abs_neg] at hdiff
  linarith

/-- The complete physical unit disk is zeta-zero-free at the native VK
width. -/
theorem riemannZeta_ne_zero_on_smoothSaddleHTVariableDisk
    {c H w t T : ℝ}
    (hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H)
    (hHeight : H ≤ |t| + T) (hw : 0 < w) (hwOne : w ≤ 1)
    (hRadius : 2 * w ≤ T)
    (hWidth : w ≤ c / GafniTao.vinogradovKorobovDenominator (|t| + T))
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    riemannZeta (smoothSaddleHTVariableDiskMap w t z) ≠ 0 := by
  intro hzeta
  let s := smoothSaddleHTVariableDiskMap w t z
  have hsReLower : 1 - w ≤ s.re :=
    smoothSaddleHTVariableDiskMap_re_lower hw.le hz
  by_cases hsRight : s.re ≤ 1
  · have hsReZero : 0 ≤ s.re := by linarith
    have hsIm := abs_smoothSaddleHTVariableDiskMap_im_le_totalHeight
      (t := t) hw.le hz hRadius
    have hsRect : s ∈ Rectangle
        ((-(1 / 2 : ℝ) : ℂ) - ((|t| + T : ℝ) : ℂ) * Complex.I)
        ((2 : ℂ) + ((|t| + T : ℝ) : ℂ) * Complex.I) := by
      constructor
      · simp only [Set.mem_preimage, sub_re, neg_re, ofReal_re, mul_re,
          ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_re,
          add_zero]
        norm_num
        exact ⟨by linarith, by linarith⟩
      · simp only [Set.mem_preimage, sub_im, neg_im, ofReal_im, mul_im,
          ofReal_re, I_im, I_re, zero_mul, mul_one, add_zero, add_im,
          neg_zero, zero_sub]
        norm_num
        rw [Set.uIcc_of_le (by
          have : 0 ≤ |t| + T := by linarith [abs_nonneg t]
          linarith)]
        have himBounds := abs_le.mp hsIm
        change -(|t| + T) ≤ s.im ∧ s.im ≤ |t| + T at himBounds
        exact ⟨by linarith [himBounds.1], himBounds.2⟩
    have hsZeroSet : s ∈ GafniTao.zeroSet 0 (|t| + T) :=
      GafniTao.mem_zeroSet_of_zeta_zero_of_fordKRectangle
        (alpha := 2) (by norm_num)
        (by linarith [abs_nonneg t]) hsRect hzeta
    have hsVK := (hZeroFree hHeight).2.2 hsZeroSet
    linarith
  · exact (riemannZeta_ne_zero_of_one_lt_re (lt_of_not_ge hsRight)) hzeta

/-- The normalized function is analytic on a neighbourhood of the closed
unit disk. -/
theorem analyticOnNhd_smoothSaddleHTVariableDiskNormalized
    {w t : ℝ} (hw : 0 < w) (hwOne : w ≤ 1) (ht : 3 < |t|) :
    AnalyticOnNhd ℂ (smoothSaddleHTVariableDiskNormalized w t)
      (Metric.closedBall (0 : ℂ) 1) := by
  intro z hz
  have hzNorm : ‖z‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, Complex.dist_eq] using hz
  have hmapOne := smoothSaddleHTVariableDiskMap_ne_one hw.le hzNorm hwOne ht
  have hmapAnalytic : AnalyticAt ℂ (smoothSaddleHTVariableDiskMap w t) z := by
    unfold smoothSaddleHTVariableDiskMap
    fun_prop
  exact analyticAt_const.mul
    ((analyticAt_riemannZeta hmapOne).comp hmapAnalytic)

/-- The centre normalization is exactly one. -/
theorem smoothSaddleHTVariableDiskNormalized_zero
    {w t : ℝ} (hcenter :
      riemannZeta (smoothSaddleHTVariableDiskCenter w t) ≠ 0) :
    smoothSaddleHTVariableDiskNormalized w t 0 = 1 := by
  rw [smoothSaddleHTVariableDiskNormalized,
    smoothSaddleHTVariableDiskMap_zero]
  exact inv_mul_cancel₀ hcenter

/-- VK zero-freeness makes the normalized zero set on the unit disk empty. -/
theorem setOfZeros_smoothSaddleHTVariableDiskNormalized_eq_empty
    {c H w t T : ℝ}
    (hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H)
    (hHeight : H ≤ |t| + T) (hw : 0 < w) (hwOne : w ≤ 1)
    (hRadius : 2 * w ≤ T)
    (hWidth : w ≤ c / GafniTao.vinogradovKorobovDenominator (|t| + T)) :
    GafniTao.SetOfZeros 1
        (smoothSaddleHTVariableDiskNormalized w t) = ∅ := by
  ext z
  constructor
  · intro hz
    have hzeta := riemannZeta_ne_zero_on_smoothSaddleHTVariableDisk
      hZeroFree hHeight hw hwOne hRadius hWidth hz.1
    have hfalse : False := hzeta (by
      have hzero := hz.2
      rw [smoothSaddleHTVariableDiskNormalized] at hzero
      exact (mul_eq_zero.mp hzero).resolve_left
        (inv_ne_zero (riemannZeta_ne_zero_of_one_lt_re (by
          simp [smoothSaddleHTVariableDiskCenter]
          linarith))))
    exact hfalse.elim
  · intro hz
    simp at hz

/-- In particular the normalized unit-disk zero set is finite, in the exact
form required by `GafniTao.FinalBound`. -/
theorem finite_setOfZeros_smoothSaddleHTVariableDiskNormalized
    {c H w t T : ℝ}
    (hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H)
    (hHeight : H ≤ |t| + T) (hw : 0 < w) (hwOne : w ≤ 1)
    (hRadius : 2 * w ≤ T)
    (hWidth : w ≤ c / GafniTao.vinogradovKorobovDenominator (|t| + T)) :
    (GafniTao.SetOfZeros 1
      (smoothSaddleHTVariableDiskNormalized w t)).Finite := by
  rw [setOfZeros_smoothSaddleHTVariableDiskNormalized_eq_empty
    hZeroFree hHeight hw hwOne hRadius hWidth]
  exact Set.finite_empty

/-- The right-of-one centre has the elementary Euler-product lower bound
`1 / (1 + 1/w)`. -/
theorem smoothSaddleHTVariableDiskCenter_lower_bound
    {w t : ℝ} (hw : 0 < w) :
    1 / (1 + 1 / w) ≤
      ‖riemannZeta (smoothSaddleHTVariableDiskCenter w t)‖ := by
  have hraw := GafniTao.ford_zeta_right_line_norm_lower
    (sigma := 1 + w) (v := t) (M := 1 + 1 / w)
    (by linarith) (by
      convert le_rfl using 1
      ring)
  simpa [smoothSaddleHTVariableDiskCenter, mul_comm] using hraw

/-- Reciprocal form of the centre lower bound. -/
theorem norm_inv_riemannZeta_smoothSaddleHTVariableDiskCenter_le
    {w t : ℝ} (hw : 0 < w) :
    ‖(riemannZeta (smoothSaddleHTVariableDiskCenter w t))⁻¹‖ ≤
      1 + 1 / w := by
  have hM : 0 < 1 + 1 / w := by positivity
  have hcenter := smoothSaddleHTVariableDiskCenter_lower_bound
    (t := t) hw
  have hcenterNe :
      riemannZeta (smoothSaddleHTVariableDiskCenter w t) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by
      simp [smoothSaddleHTVariableDiskCenter]
      linarith)
  have hcenterPos :
      0 < ‖riemannZeta (smoothSaddleHTVariableDiskCenter w t)‖ :=
    norm_pos_iff.mpr hcenterNe
  rw [norm_inv, inv_le_iff_one_le_mul₀ hcenterPos]
  have := (div_le_iff₀ hM).mp hcenter
  simpa [mul_comm] using this

/-- Every point of the physical disk is controlled by the frozen Pintz
horizontal-window majorant at total height `|t|+T`. -/
theorem norm_riemannZeta_smoothSaddleHTVariableDiskMap_le
    {w t T : ℝ} (hw : 0 < w) (hwHalf : w ≤ 1 / 2)
    (ht : 5 ≤ |t|) (hRadius : 2 * w ≤ T)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖riemannZeta (smoothSaddleHTVariableDiskMap w t z)‖ ≤
      GafniTao.pintzHorizontalZetaMajorant (w / 2) (|t| + T) := by
  let s := smoothSaddleHTVariableDiskMap w t z
  have hdiff := abs_smoothSaddleHTVariableDiskMap_im_sub_le
    (t := t) hw.le hz
  have hsImUpper := abs_smoothSaddleHTVariableDiskMap_im_le_totalHeight
    (t := t) hw.le hz hRadius
  have htTriangle : |t| ≤ |s.im| + |s.im - t| := by
    have htri := abs_add_le s.im (t - s.im)
    rw [show s.im + (t - s.im) = t by ring,
      show |t - s.im| = |s.im - t| by rw [abs_sub_comm]] at htri
    exact htri
  have hsImLower : 3 < |s.im| := by
    have hwTwo : 2 * w ≤ 1 := by linarith
    change |s.im - t| ≤ 2 * w at hdiff
    linarith
  have htotalNonneg : 0 ≤ |t| + T := by
    have hT : 0 ≤ T := by linarith
    positivity
  have hsImUpperTwo : |s.im| ≤ 2 * (|t| + T) :=
    hsImUpper.trans (by linarith)
  have hsReLower : 1 - 2 * (w / 2) ≤ s.re := by
    have := smoothSaddleHTVariableDiskMap_re_lower
      (t := t) hw.le hz
    change 1 - 2 * (w / 2) ≤ s.re
    linarith
  have hbound := GafniTao.norm_riemannZeta_le_pintzHorizontalZetaMajorant
    (eta := w / 2) (sigma := s.re) (t := s.im) (T := |t| + T)
    (by positivity) (by linarith) hsReLower hsImLower hsImUpperTwo
  have hsEq : ((s.re : ℝ) : ℂ) + Complex.I * s.im = s := by
    apply Complex.ext <;> simp
  rw [hsEq] at hbound
  exact hbound

/-- A positive normalized-disk majorant suitable for the frozen
`FinalBound` theorem. -/
noncomputable def smoothSaddleHTVariableDiskMajorant
    (w A : ℝ) : ℝ :=
  2 + (1 + 1 / w) * GafniTao.pintzHorizontalZetaMajorant (w / 2) A

theorem one_lt_smoothSaddleHTVariableDiskMajorant
    {w A : ℝ} (hw : 0 < w) (hA : 1 / 2 ≤ A) :
    1 < smoothSaddleHTVariableDiskMajorant w A := by
  have hP : 0 ≤ GafniTao.pintzHorizontalZetaMajorant (w / 2) A :=
    GafniTao.pintzHorizontalZetaMajorant_nonneg hA
  unfold smoothSaddleHTVariableDiskMajorant
  have hM : 0 ≤ 1 + 1 / w := by positivity
  nlinarith [mul_nonneg hM hP]

/-- The normalized zeta function is bounded by the positive majorant on the
closed unit disk. -/
theorem norm_smoothSaddleHTVariableDiskNormalized_le
    {w t T : ℝ} (hw : 0 < w) (hwHalf : w ≤ 1 / 2)
    (ht : 5 ≤ |t|) (hRadius : 2 * w ≤ T)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖smoothSaddleHTVariableDiskNormalized w t z‖ ≤
      smoothSaddleHTVariableDiskMajorant w (|t| + T) := by
  have hnum := norm_riemannZeta_smoothSaddleHTVariableDiskMap_le
    hw hwHalf ht hRadius hz
  have hden :=
    norm_inv_riemannZeta_smoothSaddleHTVariableDiskCenter_le
      (t := t) hw
  have hP : 0 ≤ GafniTao.pintzHorizontalZetaMajorant
      (w / 2) (|t| + T) := by
    apply GafniTao.pintzHorizontalZetaMajorant_nonneg
    have hT : 0 ≤ T := by linarith
    linarith [ht]
  rw [smoothSaddleHTVariableDiskNormalized, norm_mul]
  calc
    ‖(riemannZeta (smoothSaddleHTVariableDiskCenter w t))⁻¹‖ *
        ‖riemannZeta (smoothSaddleHTVariableDiskMap w t z)‖ ≤
      (1 + 1 / w) *
        GafniTao.pintzHorizontalZetaMajorant (w / 2) (|t| + T) :=
      mul_le_mul hden hnum (norm_nonneg _) (by positivity)
    _ ≤ smoothSaddleHTVariableDiskMajorant w (|t| + T) := by
      unfold smoothSaddleHTVariableDiskMajorant
      linarith

/-- The fixed numerical coefficient obtained from `GafniTao.FinalBound`
with source radius `5/6` and four nested normalized radii. -/
noncomputable def smoothSaddleHTVariableDiskLogDerivativeConstant : ℝ :=
  16 * (9 / 10 : ℝ) ^ 2 / ((9 / 10 : ℝ) - 5 / 6) ^ 3 +
    1 / (((99 / 100 : ℝ) ^ 2 / (19 / 20 : ℝ) - 19 / 20) *
      Real.log ((99 / 100 : ℝ) / (19 / 20 : ℝ)))

/-- The frozen zero-aware logarithmic-derivative estimate, now with an
empty zero sum on the native VK disk. -/
theorem norm_smoothSaddleHTVariableDiskNormalized_logDeriv_source_le
    {c H w beta t T : ℝ}
    (hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H)
    (hHeight : H ≤ |t| + T) (hw : 0 < w) (hwHalf : w ≤ 1 / 2)
    (ht : 5 ≤ |t|) (hRadius : 2 * w ≤ T)
    (hWidth : w ≤ c / GafniTao.vinogradovKorobovDenominator (|t| + T))
    (hbeta : 0 ≤ beta) (hbetaUpper : beta ≤ 2 * w / 3) :
    ‖deriv (smoothSaddleHTVariableDiskNormalized w t)
          (smoothSaddleHTVariableDiskSourceCoord w beta) /
        smoothSaddleHTVariableDiskNormalized w t
          (smoothSaddleHTVariableDiskSourceCoord w beta)‖ ≤
      smoothSaddleHTVariableDiskLogDerivativeConstant *
        Real.log (smoothSaddleHTVariableDiskMajorant w (|t| + T)) := by
  let f := smoothSaddleHTVariableDiskNormalized w t
  let z := smoothSaddleHTVariableDiskSourceCoord w beta
  let B := smoothSaddleHTVariableDiskMajorant w (|t| + T)
  have hwOne : w ≤ 1 := hwHalf.trans (by norm_num)
  have hT : 0 ≤ T := by linarith
  have htotalHalf : 1 / 2 ≤ |t| + T := by linarith [abs_nonneg t]
  have hB : 1 < B := by
    exact one_lt_smoothSaddleHTVariableDiskMajorant hw htotalHalf
  have hzNorm : ‖z‖ ≤ 5 / 6 := by
    exact norm_smoothSaddleHTVariableDiskSourceCoord_le hw hbeta hbetaUpper
  have hfinite : (GafniTao.SetOfZeros 1 f).Finite := by
    exact finite_setOfZeros_smoothSaddleHTVariableDiskNormalized
      hZeroFree hHeight hw hwOne hRadius hWidth
  have hzeroSet : GafniTao.SetOfZeros 1 f = ∅ := by
    exact setOfZeros_smoothSaddleHTVariableDiskNormalized_eq_empty
      hZeroFree hHeight hw hwOne hRadius hWidth
  have hcenter :
      riemannZeta (smoothSaddleHTVariableDiskCenter w t) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by
      simp [smoothSaddleHTVariableDiskCenter]
      linarith)
  have hbound := GafniTao.FinalBound
    (B := B) (r' := (5 / 6 : ℝ)) (r := (9 / 10 : ℝ))
    (R' := (19 / 20 : ℝ)) (R := (99 / 100 : ℝ))
    (f := f) (z := z)
    hB (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
    (by
      exact analyticOnNhd_smoothSaddleHTVariableDiskNormalized
        hw hwOne (by linarith))
    (by
      exact smoothSaddleHTVariableDiskNormalized_zero hcenter)
    hfinite
    (by
      intro u hu
      exact norm_smoothSaddleHTVariableDiskNormalized_le
        hw hwHalf ht hRadius (hu.trans (by norm_num)))
    (by
      constructor
      · simpa [Metric.mem_closedBall, Complex.dist_eq] using hzNorm
      · intro hzLarge
        have hzUnit : z ∈ GafniTao.SetOfZeros 1 f :=
          ⟨hzLarge.1.trans (by norm_num), hzLarge.2⟩
        rw [hzeroSet] at hzUnit
        exact hzUnit)
  have hsmallEmpty : GafniTao.SetOfZeros (9 / 10) f = ∅ := by
    ext rho
    constructor
    · intro hrho
      have hrhoUnit : rho ∈ GafniTao.SetOfZeros 1 f :=
        ⟨hrho.1.trans (by norm_num), hrho.2⟩
      rw [hzeroSet] at hrhoUnit
      exact hrhoUnit
    · intro hrho
      simp at hrho
  have hfinset :
      (GafniTao.finiteSetOfZeros_mono
        (by norm_num : (9 / 10 : ℝ) < 1) hfinite).toFinset = ∅ := by
    ext rho
    constructor
    · intro hrho
      have hrhoSet := (GafniTao.finiteSetOfZeros_mono
        (by norm_num : (9 / 10 : ℝ) < 1) hfinite).mem_toFinset.mp hrho
      rw [hsmallEmpty] at hrhoSet
      simp at hrhoSet
    · intro hrho
      simp at hrho
  rw [hfinset] at hbound
  simpa [f, z, B, smoothSaddleHTVariableDiskLogDerivativeConstant] using hbound

/-- The affine normalization multiplies the physical zeta logarithmic
derivative by exactly `2w`. -/
theorem logDeriv_smoothSaddleHTVariableDiskNormalized_eq
    {w t : ℝ} {z : ℂ} (hw : 0 < w)
    (hmapOne : smoothSaddleHTVariableDiskMap w t z ≠ 1)
    (hzeta : riemannZeta (smoothSaddleHTVariableDiskMap w t z) ≠ 0) :
    deriv (smoothSaddleHTVariableDiskNormalized w t) z /
        smoothSaddleHTVariableDiskNormalized w t z =
      ((2 * w : ℝ) : ℂ) *
        (deriv riemannZeta (smoothSaddleHTVariableDiskMap w t z) /
          riemannZeta (smoothSaddleHTVariableDiskMap w t z)) := by
  have hmapDiff : DifferentiableAt ℂ
      (smoothSaddleHTVariableDiskMap w t) z := by
    unfold smoothSaddleHTVariableDiskMap
    fun_prop
  have hzetaDiff : DifferentiableAt ℂ riemannZeta
      (smoothSaddleHTVariableDiskMap w t z) :=
    (analyticAt_riemannZeta hmapOne).differentiableAt
  have hcompDiff : DifferentiableAt ℂ
      (fun u ↦ riemannZeta (smoothSaddleHTVariableDiskMap w t u)) z :=
    hzetaDiff.comp z hmapDiff
  change deriv (fun u ↦
      (riemannZeta (smoothSaddleHTVariableDiskCenter w t))⁻¹ *
        riemannZeta (smoothSaddleHTVariableDiskMap w t u)) z /
      ((riemannZeta (smoothSaddleHTVariableDiskCenter w t))⁻¹ *
        riemannZeta (smoothSaddleHTVariableDiskMap w t z)) = _
  rw [deriv_const_mul
    (riemannZeta (smoothSaddleHTVariableDiskCenter w t))⁻¹ hcompDiff]
  have hderivComp :
      deriv (fun u ↦ riemannZeta
          (smoothSaddleHTVariableDiskMap w t u)) z =
        deriv riemannZeta (smoothSaddleHTVariableDiskMap w t z) *
          deriv (smoothSaddleHTVariableDiskMap w t) z := by
    simpa only [Function.comp_apply] using
      (deriv_comp z hzetaDiff hmapDiff)
  have hmapDeriv :
      deriv (smoothSaddleHTVariableDiskMap w t) z =
        ((2 * w : ℝ) : ℂ) := by
    unfold smoothSaddleHTVariableDiskMap
    simp
  rw [hderivComp, hmapDeriv]
  have hcenter : riemannZeta
      (smoothSaddleHTVariableDiskCenter w t) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by
      simp [smoothSaddleHTVariableDiskCenter]
      linarith)
  have hcenterInv :
      (riemannZeta (smoothSaddleHTVariableDiskCenter w t))⁻¹ ≠ 0 :=
    inv_ne_zero hcenter
  field_simp

/-- Physical high-height bound delivered by the zero-free variable disk.
The remaining task is purely real asymptotic control of the displayed
majorant. -/
theorem norm_riemannZeta_logDeriv_smoothSaddleHTSourceExponent_le_variableDisk
    {c H w beta t T : ℝ}
    (hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H)
    (hHeight : H ≤ |t| + T) (hw : 0 < w) (hwHalf : w ≤ 1 / 2)
    (ht : 5 ≤ |t|) (hRadius : 2 * w ≤ T)
    (hWidth : w ≤ c / GafniTao.vinogradovKorobovDenominator (|t| + T))
    (hbeta : 0 ≤ beta) (hbetaUpper : beta ≤ 2 * w / 3) :
    ‖deriv riemannZeta (smoothSaddleHTSourceExponent beta t) /
        riemannZeta (smoothSaddleHTSourceExponent beta t)‖ ≤
      smoothSaddleHTVariableDiskLogDerivativeConstant *
          Real.log (smoothSaddleHTVariableDiskMajorant w (|t| + T)) /
        (2 * w) := by
  let z := smoothSaddleHTVariableDiskSourceCoord w beta
  have hwOne : w ≤ 1 := hwHalf.trans (by norm_num)
  have hzNorm : ‖z‖ ≤ 5 / 6 :=
    norm_smoothSaddleHTVariableDiskSourceCoord_le hw hbeta hbetaUpper
  have hzNormOne : ‖z‖ ≤ 1 := hzNorm.trans (by norm_num)
  have hmapOne := smoothSaddleHTVariableDiskMap_ne_one
    hw.le hzNormOne hwOne (by linarith : 3 < |t|)
  have hzeta := riemannZeta_ne_zero_on_smoothSaddleHTVariableDisk
    hZeroFree hHeight hw hwOne hRadius hWidth hzNormOne
  have htransport := logDeriv_smoothSaddleHTVariableDiskNormalized_eq
    hw hmapOne hzeta
  have hnorm :=
    norm_smoothSaddleHTVariableDiskNormalized_logDeriv_source_le
      hZeroFree hHeight hw hwHalf ht hRadius hWidth hbeta hbetaUpper
  dsimp [z] at htransport
  have hmapSource := smoothSaddleHTVariableDiskMap_sourceCoord
    (w := w) (beta := beta) (t := t) hw
  rw [hmapSource] at htransport
  rw [htransport, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 2 * w)] at hnorm
  rw [le_div_iff₀ (by positivity : 0 < 2 * w)]
  simpa [mul_comm] using hnorm

end

end Tao2026
