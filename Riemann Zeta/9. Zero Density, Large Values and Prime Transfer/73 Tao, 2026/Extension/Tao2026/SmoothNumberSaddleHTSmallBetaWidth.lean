import Tao2026.SmoothNumberSaddleHTContourWidth
import Tao2026.SmoothNumberSaddleHTShiftedTwoPole
import Tao2026.SmoothNumberSaddleHTLogDerivativeLowHeight

/-!
# Native contour width in the small-beta branch

For `beta <= 2 * eta`, the negative-left two-pole rectangle has physical
depth `beta + eta <= 3 * eta`.  This module spends the fixed factor three in
the asymptotic Vinogradov--Korobov comparison and packages the resulting
exact decomposition with every zero-free premise discharged eventually in
`y`, uniformly throughout the full HT frequency range.
-/

open Filter Topology MeasureTheory Set Complex Finset
open scoped ArithmeticFunction.vonMangoldt BigOperators Interval

namespace Tao2026

noncomputable section

/-- The selected displacement tends to zero, with an arbitrary positive
target coefficient. -/
theorem eventually_smoothSaddleHTContourShift_le_const
    {A epsilon : ℝ} (hA : 0 < A) (hEpsilonOne : epsilon < 1) :
    ∀ᶠ y : ℕ in atTop,
      smoothSaddleHTContourShift y epsilon ≤ A := by
  have hlogTop : Tendsto (fun y : ℕ => Real.log (y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hp : 0 < 1 - epsilon / 2 := by linarith
  have hsmall :=
    ((tendsto_rpow_neg_atTop hp).const_mul 2).comp hlogTop
  have hsmall' : Tendsto
      (fun y : ℕ => 2 * Real.log (y : ℝ) ^ (-(1 - epsilon / 2)))
      atTop (𝓝 0) := by
    simpa using hsmall
  have hbound := hsmall'.eventually (eventually_le_nhds hA)
  filter_upwards [hbound, eventually_ge_atTop (2 : ℕ)] with y hy htwo
  have hlogPos : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  unfold smoothSaddleHTContourShift
  rw [show epsilon / 2 - 1 = -(1 - epsilon / 2) by ring]
  exact hy

/-- In the small-beta branch, the full physical depth is eventually at most
one, as required by the native zero-free rectangle. -/
theorem eventually_three_mul_smoothSaddleHTContourShift_le_one
    {epsilon : ℝ} (hEpsilonOne : epsilon < 1) :
    ∀ᶠ y : ℕ in atTop,
      3 * smoothSaddleHTContourShift y epsilon ≤ 1 := by
  filter_upwards
      [eventually_smoothSaddleHTContourShift_le_const
        (A := (1 / 3 : ℝ)) (by norm_num) hEpsilonOne] with y hy
  nlinarith

/-- The factor-three small-beta depth still fits the native VK width at the
actual translated contour height, uniformly over the source frequency. -/
theorem eventually_three_mul_smoothSaddleHTContourShift_le_vk_actualHeight
    {c epsilon : ℝ} (hc : 0 < c)
    (hEpsilon : 0 < epsilon) (hEpsilonOne : epsilon < 1) :
    ∀ᶠ y : ℕ in atTop, ∀ t : ℝ,
      |t| ≤ smoothSaddleHTFrequencyCeiling y epsilon →
      3 * smoothSaddleHTContourShift y epsilon ≤ c /
        GafniTao.vinogradovKorobovDenominator
          (|t| + smoothSaddleHTContourHeight y epsilon) := by
  have hcThird : 0 < c / 3 := by positivity
  filter_upwards
      [eventually_smoothSaddleHTContourShift_le_vk_actualHeight
        hcThird hEpsilon hEpsilonOne] with y hy
  intro t ht
  have hwidth := hy t ht
  calc
    3 * smoothSaddleHTContourShift y epsilon <=
        3 * ((c / 3) /
          GafniTao.vinogradovKorobovDenominator
            (abs t + smoothSaddleHTContourHeight y epsilon)) :=
      mul_le_mul_of_nonneg_left hwidth (by norm_num)
    _ = c / GafniTao.vinogradovKorobovDenominator
          (|t| + smoothSaddleHTContourHeight y epsilon) := by ring

/-- On any admissible negative-left VK rectangle, the Perron-kernel residue
is exactly the negative physical zeta logarithmic derivative at the source
point.  This exposes the analytic quantity that remains to be bounded in the
small-beta branch. -/
theorem smoothSaddleHTShiftedOriginResidue_sourceExponent_eq_neg_logDeriv_of_vK
    {c H beta eta t T right : ℝ}
    (hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H)
    (heta : 0 < eta) (hbeta : 0 < beta) (hbetaRight : beta < right)
    (ht : |t| < T) (hdepthOne : beta + eta ≤ 1)
    (hHeight : H ≤ |t| + T)
    (hWidth : beta + eta ≤ c /
      GafniTao.vinogradovKorobovDenominator (|t| + T)) :
    smoothSaddleHTShiftedOriginResidue
        (smoothSaddleHTSourceExponent beta t) =
      -logDeriv riemannZeta (smoothSaddleHTSourceExponent beta t) := by
  have hT : 0 ≤ T := by linarith [abs_nonneg t]
  have hleftRight : -eta ≤ right := by linarith
  have hsurAll :=
    smoothSaddleHTSource_shiftedSurrogate_ne_zero_on_rectangle_of_vK_left
      (left := -eta) (right := right) (beta := beta) (t := t) (T := T)
      hZeroFree (by simpa using hdepthOne) hleftRight hT hHeight
        (by simpa using hWidth)
  have hzeroMem : (0 : ℂ) ∈ Rectangle
      (((-eta : ℝ) : ℂ) - (T : ℂ) * Complex.I)
      ((right : ℂ) + (T : ℂ) * Complex.I) := by
    constructor
    · simp only [Set.mem_preimage, sub_re, ofReal_re, mul_re, ofReal_im,
        I_re, I_im, mul_zero, zero_mul, sub_zero, add_re, add_zero]
      norm_num
      rw [Set.uIcc_of_le hleftRight]
      exact ⟨by linarith, by linarith⟩
    · simp only [Set.mem_preimage, sub_im, ofReal_im, mul_im, ofReal_re,
        I_im, I_re, zero_mul, mul_one, add_zero, add_im]
      norm_num
      rw [Set.uIcc_of_le (by linarith)]
      exact ⟨by linarith, hT⟩
  have hsur : GafniTao.sharpZetaSurrogate
      (smoothSaddleHTSourceExponent beta t) ≠ 0 := by
    simpa using hsurAll 0 hzeroMem
  have hs1 : smoothSaddleHTSourceExponent beta t ≠ 1 := by
    intro hs
    have hre := congrArg Complex.re hs
    simp [smoothSaddleHTSourceExponent] at hre
    linarith
  have hzeta : riemannZeta (smoothSaddleHTSourceExponent beta t) ≠ 0 := by
    intro hzeta
    exact hsur ((GafniTao.sharpZetaSurrogate_eq_zero_iff hs1).2 hzeta)
  exact smoothSaddleHTShiftedOriginResidue_eq hs1 hzeta

/-- At bounded physical height, compactness of the entire surrogate bounds
the small-beta origin residue by the expected simple-pole scale. -/
theorem exists_norm_smoothSaddleHTShiftedOriginResidue_lowHeight_le
    {c H : ℝ} (hc : 0 < c)
    (hH : Real.exp (Real.exp 1) ≤ H)
    (hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H) :
    ∃ C : ℝ, 0 < C ∧ ∀ {beta t : ℝ},
      0 < beta →
      beta ≤ c / (2 * GafniTao.vinogradovKorobovDenominator H) →
      |t| ≤ H →
      ‖smoothSaddleHTShiftedOriginResidue
          (smoothSaddleHTSourceExponent beta t)‖ ≤ C + 1 / beta := by
  obtain ⟨C, hC, hlog⟩ :=
    exists_norm_riemannZeta_logDeriv_lowHeight_leftLine_le
      hc hH hZeroFree
  refine ⟨C, hC, ?_⟩
  intro beta t hbeta hbetaWidth ht
  let s : ℂ := smoothSaddleHTSourceExponent beta t
  have hsCompact : s ∈ smoothSaddleHTLowHeightCompact c H := by
    change s.re ∈ Set.Icc
        (1 - c / (2 * GafniTao.vinogradovKorobovDenominator H)) 2 ∧
      s.im ∈ Set.Icc (-H) H
    have hsRe : s.re = 1 - beta := by
      simp [s, smoothSaddleHTSourceExponent]
    have hsIm : s.im = t := by
      simp [s, smoothSaddleHTSourceExponent]
    rw [hsRe, hsIm]
    exact ⟨⟨by linarith, by linarith⟩, abs_le.mp ht⟩
  have hs1 : s ≠ 1 := by
    intro hs
    have hre := congrArg Complex.re hs
    simp [s, smoothSaddleHTSourceExponent] at hre
    linarith
  have hsur : GafniTao.sharpZetaSurrogate s ≠ 0 :=
    sharpZetaSurrogate_ne_zero_on_smoothSaddleHTLowHeightCompact
      hc hH hZeroFree hsCompact
  have hzeta : riemannZeta s ≠ 0 := by
    intro hzeta
    exact hsur ((GafniTao.sharpZetaSurrogate_eq_zero_iff hs1).2 hzeta)
  rw [show smoothSaddleHTShiftedOriginResidue
      (smoothSaddleHTSourceExponent beta t) = -logDeriv riemannZeta s by
        exact smoothSaddleHTShiftedOriginResidue_eq hs1 hzeta,
    norm_neg]
  simpa [s, smoothSaddleHTSourceExponent, logDeriv_apply] using
    hlog (eta := beta) (R := t) hbeta hbetaWidth ht

/-- Native VK constants and an eventual exact two-pole decomposition for
the complete small-beta branch `0 < beta <= 2 * eta`. -/
theorem exists_smoothSaddleHT_native_eventually_exact_smallBeta_decomposition
    {epsilon : ℝ} (hEpsilon : 0 < epsilon)
    (hEpsilonOne : epsilon < 1) :
    ∃ c H : ℝ, 0 < c ∧ Real.exp (Real.exp 1) ≤ H ∧
      GafniTao.VinogradovKorobovRectangleZeroFree c H ∧
      ∀ᶠ y : ℕ in atTop, ∀ beta t : ℝ,
        0 < beta →
        beta ≤ 2 * smoothSaddleHTContourShift y epsilon →
        |t| ≤ smoothSaddleHTFrequencyCeiling y epsilon →
        smoothSaddleHTShiftedOriginResidue
            (smoothSaddleHTSourceExponent beta t) =
              -logDeriv riemannZeta
                (smoothSaddleHTSourceExponent beta t) ∧
          smoothSaddleHTMangoldtTransform y beta t -
              smoothSaddleHTMangoldtMainTerm y beta t =
            smoothSaddleHTShiftedOriginResidue
                (smoothSaddleHTSourceExponent beta t) +
              smoothSaddleHTSmallBetaContourEdgeContribution
                y beta epsilon t -
                smoothSaddleHTContourTruncationError y beta epsilon t := by
  obtain ⟨c, H, hc, hH, hZeroFree⟩ :=
    exists_smoothSaddleHT_native_vinogradovKorobovRectangleZeroFree
  refine ⟨c, H, hc, hH, hZeroFree, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    eventually_three_mul_smoothSaddleHTContourShift_le_one hEpsilonOne,
    eventually_smoothSaddleHT_native_contourHeight (H := H) hEpsilonOne,
    eventually_three_mul_smoothSaddleHTContourShift_le_vk_actualHeight
      hc hEpsilon hEpsilonOne] with y hy hdepth hHeight hWidth
  intro beta t hbeta hbetaUpper ht
  have hshiftPos := smoothSaddleHTContourShift_pos hy epsilon
  have hdepth' : beta + smoothSaddleHTContourShift y epsilon <= 1 := by
    linarith
  have hWidth' : beta + smoothSaddleHTContourShift y epsilon <= c /
      GafniTao.vinogradovKorobovDenominator
        (|t| + smoothSaddleHTContourHeight y epsilon) := by
    exact (by linarith :
      beta + smoothSaddleHTContourShift y epsilon <=
        3 * smoothSaddleHTContourShift y epsilon) |>.trans (hWidth t ht)
  have hright := smoothSaddleHTContourRight_gt hy beta
  have htStrict : |t| < smoothSaddleHTContourHeight y epsilon :=
    ht.trans_lt (smoothSaddleHTFrequencyCeiling_lt_contourHeight y epsilon)
  constructor
  · exact
      smoothSaddleHTShiftedOriginResidue_sourceExponent_eq_neg_logDeriv_of_vK
        hZeroFree hshiftPos hbeta hright htStrict hdepth'
          (hHeight t) hWidth'
  · exact smoothSaddleHTMangoldtTransform_sub_mainTerm_eq_smallBetaContourErrors
      hZeroFree hy hbeta hdepth' ht (hHeight t) hWidth'

end

end Tao2026
