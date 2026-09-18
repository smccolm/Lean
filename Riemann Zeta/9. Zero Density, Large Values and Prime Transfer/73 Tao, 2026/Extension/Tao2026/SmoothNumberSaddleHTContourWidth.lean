import Tao2026.SmoothNumberSaddleHTContourParameters
import GafniTao.FordVKScale

/-!
# The selected HT contour fits the native VK zero-free region

This module proves the asymptotic parameter comparison left open after the
exact shifted-contour assembly.  At the source frequency ceiling the product
of the selected shift and the Vinogradov--Korobov denominator is exactly
twice `(log y)^(-epsilon/6)` times a one-third power of `log log y`, hence
tends to zero.  The frozen factor-three height comparison proves the literal
zero-free width uniformly for every requested frequency.

The final theorem selects the native Ford constants and instantiates the
exact transform-error decomposition eventually in `y`, throughout the full
HT frequency range and in the contour branch where the shift is below
`beta`.
-/

open Filter Topology MeasureTheory Set Complex Finset
open scoped ArithmeticFunction.vonMangoldt BigOperators Interval

namespace Tao2026

noncomputable section

theorem vinogradovKorobovDenominator_smoothSaddleHTFrequencyCeiling
    {y : ℕ} (hy : 2 ≤ y) {ε : ℝ} (hε : ε < 3 / 2) :
    GafniTao.vinogradovKorobovDenominator
        (smoothSaddleHTFrequencyCeiling y ε) =
      (Real.log y) ^ (1 - 2 * ε / 3) *
        (((3 / 2 - ε) * Real.log (Real.log y)) ^ (1 / 3 : ℝ)) := by
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have ha : 0 < (3 / 2 - ε) := by linarith
  unfold GafniTao.vinogradovKorobovDenominator
    smoothSaddleHTFrequencyCeiling
  rw [Real.log_exp, Real.log_rpow hlog]
  rw [← Real.rpow_mul hlog.le]
  congr 2
  ring

theorem smoothSaddleHTContourShift_mul_vinogradovKorobovDenominator
    {y : ℕ} (hy : 2 ≤ y) {ε : ℝ}
    (hε : ε < 3 / 2) :
    smoothSaddleHTContourShift y ε *
        GafniTao.vinogradovKorobovDenominator
          (smoothSaddleHTFrequencyCeiling y ε) =
      (Real.log y) ^ (-ε / 6) *
        (2 * (((3 / 2 - ε) * Real.log (Real.log y)) ^ (1 / 3 : ℝ))) := by
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  rw [vinogradovKorobovDenominator_smoothSaddleHTFrequencyCeiling hy hε]
  unfold smoothSaddleHTContourShift
  calc
    2 * (Real.log y) ^ (ε / 2 - 1) *
          ((Real.log y) ^ (1 - 2 * ε / 3) *
            (((3 / 2 - ε) * Real.log (Real.log y)) ^ (1 / 3 : ℝ))) =
        2 * ((Real.log y) ^ (ε / 2 - 1) *
          (Real.log y) ^ (1 - 2 * ε / 3)) *
            (((3 / 2 - ε) * Real.log (Real.log y)) ^ (1 / 3 : ℝ)) := by ring
    _ = 2 * (Real.log y) ^ ((ε / 2 - 1) + (1 - 2 * ε / 3)) *
          (((3 / 2 - ε) * Real.log (Real.log y)) ^ (1 / 3 : ℝ)) := by
      rw [Real.rpow_add hlog]
    _ = (Real.log y) ^ (-ε / 6) *
          (2 * (((3 / 2 - ε) * Real.log (Real.log y)) ^ (1 / 3 : ℝ))) := by
      rw [show (ε / 2 - 1) + (1 - 2 * ε / 3) = -ε / 6 by ring]
      ring

theorem eventually_four_mul_smoothSaddleHTVKFactor_le
    {c ε : ℝ} (hc : 0 < c)
    (hε : 0 < ε) (hεOne : ε < 1) :
    ∀ᶠ x : ℝ in atTop,
      4 * x ^ (-ε / 6) *
          (((3 / 2 - ε) * Real.log x) ^ (1 / 3 : ℝ)) ≤ c := by
  have ha : 0 < (3 / 2 - ε) := by linarith
  have hp : 0 < ε / 6 := by positivity
  have hsmall :=
    (isLittleO_log_rpow_rpow_atTop (1 / 3 : ℝ) hp).const_mul_left
      (4 * (3 / 2 - ε) ^ (1 / 3 : ℝ))
  have hbound := hsmall.bound hc
  filter_upwards [hbound, eventually_ge_atTop (Real.exp 1)] with x hx hbase
  have hxPos : 0 < x := (Real.exp_pos 1).trans_le hbase
  have hlogOne : 1 ≤ Real.log x := by
    simpa only [Real.log_exp] using
      Real.strictMonoOn_log.monotoneOn (Real.exp_pos 1) hxPos hbase
  have hlogNonneg : 0 ≤ Real.log x := zero_le_one.trans hlogOne
  have haPow : 0 ≤ (3 / 2 - ε) ^ (1 / 3 : ℝ) :=
    Real.rpow_nonneg ha.le _
  have hlogPow : 0 ≤ Real.log x ^ (1 / 3 : ℝ) :=
    Real.rpow_nonneg hlogNonneg _
  have hxPow : 0 < x ^ (ε / 6) := Real.rpow_pos_of_pos hxPos _
  rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) haPow) hlogPow),
    Real.norm_eq_abs, abs_of_pos hxPow] at hx
  rw [Real.mul_rpow ha.le hlogNonneg]
  rw [show -ε / 6 = -(ε / 6) by ring, Real.rpow_neg hxPos.le]
  calc
    4 * (x ^ (ε / 6))⁻¹ *
          ((3 / 2 - ε) ^ (1 / 3 : ℝ) *
            Real.log x ^ (1 / 3 : ℝ)) =
        (4 * (3 / 2 - ε) ^ (1 / 3 : ℝ) *
          Real.log x ^ (1 / 3 : ℝ)) / x ^ (ε / 6) := by ring
    _ ≤ c := (div_le_iff₀ hxPow).2 (by simpa [mul_assoc] using hx)

theorem eventually_smoothSaddleHTContourShift_le_vk_three_frequency
    {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (hεOne : ε < 1) :
    ∀ᶠ y : ℕ in atTop,
      smoothSaddleHTContourShift y ε ≤ c /
        GafniTao.vinogradovKorobovDenominator
          (3 * smoothSaddleHTFrequencyCeiling y ε) := by
  have ha : 0 < (3 / 2 - ε) := by linarith
  have hlogTop : Tendsto (fun y : ℕ => Real.log (y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpowerTop : Tendsto
      (fun y : ℕ => Real.log (y : ℝ) ^ (3 / 2 - ε)) atTop atTop :=
    (tendsto_rpow_atTop ha).comp hlogTop
  have hYTop : Tendsto (fun y : ℕ => smoothSaddleHTFrequencyCeiling y ε)
      atTop atTop := by
    simpa only [smoothSaddleHTFrequencyCeiling] using
      Real.tendsto_exp_atTop.comp hpowerTop
  have hthreeYTop : Tendsto
      (fun y : ℕ => 3 * smoothSaddleHTFrequencyCeiling y ε)
      atTop atTop := hYTop.const_mul_atTop (by norm_num)
  have hcHalf : 0 < c / 2 := by positivity
  have hprod := hlogTop.eventually
    (eventually_four_mul_smoothSaddleHTVKFactor_le hcHalf hε hεOne)
  have hY100 := hYTop.eventually (eventually_ge_atTop (100 : ℝ))
  have hloglog9 :=
    (GafniTao.tendsto_fordVKLogLog_atTop.comp hYTop).eventually
      (eventually_ge_atTop (9 : ℝ))
  have hbase := hthreeYTop.eventually
    (eventually_ge_atTop (Real.exp (Real.exp 1)))
  filter_upwards [eventually_ge_atTop (2 : ℕ), hprod, hY100, hloglog9,
    hbase] with y hy hprod hY100 hloglog9 hbase
  have hscale := GafniTao.vinogradovKorobovDenominator_mul_le_four
    hY100 hloglog9 (q := (3 : ℝ)) (by norm_num) (by norm_num)
  have hDpos := GafniTao.vinogradovKorobovDenominator_pos hbase
  rw [le_div_iff₀ hDpos]
  calc
    smoothSaddleHTContourShift y ε *
        GafniTao.vinogradovKorobovDenominator
          (3 * smoothSaddleHTFrequencyCeiling y ε) ≤
      smoothSaddleHTContourShift y ε *
        (4 * GafniTao.vinogradovKorobovDenominator
          (smoothSaddleHTFrequencyCeiling y ε)) :=
      mul_le_mul_of_nonneg_left hscale
        (smoothSaddleHTContourShift_pos hy ε).le
    _ = 8 * ((Real.log y) ^ (-ε / 6) *
        (((3 / 2 - ε) * Real.log (Real.log y)) ^ (1 / 3 : ℝ))) := by
      rw [show smoothSaddleHTContourShift y ε *
          (4 * GafniTao.vinogradovKorobovDenominator
            (smoothSaddleHTFrequencyCeiling y ε)) =
          4 * (smoothSaddleHTContourShift y ε *
            GafniTao.vinogradovKorobovDenominator
              (smoothSaddleHTFrequencyCeiling y ε)) by ring,
        smoothSaddleHTContourShift_mul_vinogradovKorobovDenominator
          hy (by linarith : ε < 3 / 2)]
      ring
    _ ≤ c := by nlinarith [hprod]

theorem eventually_smoothSaddleHTContourShift_le_vk_actualHeight
    {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (hεOne : ε < 1) :
    ∀ᶠ y : ℕ in atTop, ∀ t : ℝ,
      |t| ≤ smoothSaddleHTFrequencyCeiling y ε →
      smoothSaddleHTContourShift y ε ≤ c /
        GafniTao.vinogradovKorobovDenominator
          (|t| + smoothSaddleHTContourHeight y ε) := by
  have ha : 0 < (3 / 2 - ε) := by linarith
  have hlogTop : Tendsto (fun y : ℕ => Real.log (y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hYTop : Tendsto (fun y : ℕ => smoothSaddleHTFrequencyCeiling y ε)
      atTop atTop := by
    simpa only [smoothSaddleHTFrequencyCeiling] using
      Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop ha).comp hlogTop)
  filter_upwards
    [eventually_smoothSaddleHTContourShift_le_vk_three_frequency hc hε hεOne,
    hYTop.eventually
      (eventually_ge_atTop (Real.exp (Real.exp 1)))] with y hwidth hYbase
  intro t ht
  have hactualUpper := smoothSaddleHT_totalHeight_le ht
  have hactualBase : Real.exp (Real.exp 1) ≤
      |t| + smoothSaddleHTContourHeight y ε := by
    unfold smoothSaddleHTContourHeight
    nlinarith [abs_nonneg t]
  have hactualExpOne : Real.exp 1 ≤
      |t| + smoothSaddleHTContourHeight y ε :=
    (le_trans (by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by norm_num)) hactualBase)
  have hthreeExpOne : Real.exp 1 ≤
      3 * smoothSaddleHTFrequencyCeiling y ε :=
    hactualExpOne.trans hactualUpper
  have hmono := GafniTao.monotoneOn_vinogradovKorobovDenominator
    hactualExpOne hthreeExpOne hactualUpper
  have hDactual := GafniTao.vinogradovKorobovDenominator_pos hactualBase
  exact hwidth.trans (div_le_div_of_nonneg_left hc.le hDactual hmono)

theorem eventually_smoothSaddleHTContourShift_le_one
    {ε : ℝ} (hεOne : ε < 1) :
    ∀ᶠ y : ℕ in atTop, smoothSaddleHTContourShift y ε ≤ 1 := by
  have hlogTop : Tendsto (fun y : ℕ => Real.log (y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hp : 0 < 1 - ε / 2 := by linarith
  have hsmall :=
    ((tendsto_rpow_neg_atTop hp).const_mul 2).comp hlogTop
  have hsmall' : Tendsto
      (fun y : ℕ => 2 * Real.log (y : ℝ) ^ (-(1 - ε / 2)))
      atTop (𝓝 0) := by simpa using hsmall
  have hbound := hsmall'.eventually
    (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hbound, eventually_ge_atTop (2 : ℕ)] with y hy htwo
  have hlogPos : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  unfold smoothSaddleHTContourShift
  rw [show ε / 2 - 1 = -(1 - ε / 2) by ring]
  exact hy

theorem eventually_smoothSaddleHT_native_contourHeight
    {H ε : ℝ} (hεOne : ε < 1) :
    ∀ᶠ y : ℕ in atTop, ∀ t : ℝ,
      H ≤ |t| + smoothSaddleHTContourHeight y ε := by
  have ha : 0 < (3 / 2 - ε) := by linarith
  have hlogTop : Tendsto (fun y : ℕ => Real.log (y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hYTop : Tendsto (fun y : ℕ => smoothSaddleHTFrequencyCeiling y ε)
      atTop atTop := by
    simpa only [smoothSaddleHTFrequencyCeiling] using
      Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop ha).comp hlogTop)
  filter_upwards [hYTop.eventually (eventually_ge_atTop H)] with y hy
  intro t
  have hYpos := smoothSaddleHTFrequencyCeiling_pos y ε
  unfold smoothSaddleHTContourHeight
  nlinarith [abs_nonneg t]

theorem exists_smoothSaddleHT_native_eventually_exact_decomposition
    {ε : ℝ} (hε : 0 < ε) (hεOne : ε < 1) :
    ∃ c H : ℝ, 0 < c ∧ Real.exp (Real.exp 1) ≤ H ∧
      GafniTao.VinogradovKorobovRectangleZeroFree c H ∧
      ∀ᶠ y : ℕ in atTop, ∀ beta t : ℝ,
        smoothSaddleHTContourShift y ε < beta →
        |t| ≤ smoothSaddleHTFrequencyCeiling y ε →
        smoothSaddleHTMangoldtTransform y beta t -
            smoothSaddleHTMangoldtMainTerm y beta t =
          smoothSaddleHTContourEdgeContribution y beta ε t -
            smoothSaddleHTContourTruncationError y beta ε t := by
  obtain ⟨c, H, hc, hH, hZeroFree⟩ :=
    exists_smoothSaddleHT_native_vinogradovKorobovRectangleZeroFree
  refine ⟨c, H, hc, hH, hZeroFree, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    eventually_smoothSaddleHTContourShift_le_one hεOne,
    eventually_smoothSaddleHT_native_contourHeight (H := H) hεOne,
    eventually_smoothSaddleHTContourShift_le_vk_actualHeight hc hε hεOne] with
      y hy hshiftOne hHeight hWidth
  intro beta t hbeta ht
  exact smoothSaddleHTMangoldtTransform_sub_mainTerm_eq_contourErrors
    hZeroFree hy hbeta hshiftOne ht (hHeight t) (hWidth t ht)

end

end Tao2026
