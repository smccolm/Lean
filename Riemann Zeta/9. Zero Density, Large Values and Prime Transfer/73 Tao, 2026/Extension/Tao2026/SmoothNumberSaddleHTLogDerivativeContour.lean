import Tao2026.SmoothNumberSaddleHTLogDerivativeLowHeight

/-!
# Logarithmic derivative in HT contour coordinates

The physical ordinates on the two horizontal edges lie between one and
three source frequency ceilings in absolute value.  The Landau estimate at
such an ordinate asks for VK width at three times that height, hence at most
nine source ceilings.  This module proves the required asymptotic width and
packages the sign-uniform estimate with a single source-scale majorant.
-/

open Complex Filter Set Topology
open RiemannZeta.GuthMaynard

namespace Tao2026

noncomputable section

/-- Twice the HT shift fits eventually inside the native VK width even at
nine times the source frequency ceiling. -/
theorem eventually_two_mul_smoothSaddleHTContourShift_le_vk_nine_frequency
    {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (hεOne : ε < 1) :
    ∀ᶠ y : ℕ in atTop,
      2 * smoothSaddleHTContourShift y ε ≤ c /
        GafniTao.vinogradovKorobovDenominator
          (9 * smoothSaddleHTFrequencyCeiling y ε) := by
  have hcEight : 0 < c / 8 := by positivity
  have ha : 0 < (3 / 2 - ε) := by linarith
  have hlogTop : Tendsto (fun y : ℕ => Real.log (y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hYTop : Tendsto (fun y : ℕ => smoothSaddleHTFrequencyCeiling y ε)
      atTop atTop := by
    simpa only [smoothSaddleHTFrequencyCeiling] using
      Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop ha).comp hlogTop)
  have hthreeYTop : Tendsto
      (fun y : ℕ => 3 * smoothSaddleHTFrequencyCeiling y ε)
      atTop atTop := hYTop.const_mul_atTop (by norm_num)
  filter_upwards
    [eventually_smoothSaddleHTContourShift_le_vk_three_frequency
      hcEight hε hεOne,
     hthreeYTop.eventually (eventually_ge_atTop (100 : ℝ)),
     (GafniTao.tendsto_fordVKLogLog_atTop.comp hthreeYTop).eventually
       (eventually_ge_atTop (9 : ℝ)),
     hthreeYTop.eventually
       (eventually_ge_atTop (Real.exp (Real.exp 1))),
     eventually_ge_atTop (2 : ℕ)] with y hwidth hthree100 hloglog hthreeBase hy
  let Y := smoothSaddleHTFrequencyCeiling y ε
  have hscale : GafniTao.vinogradovKorobovDenominator (9 * Y) ≤
      4 * GafniTao.vinogradovKorobovDenominator (3 * Y) := by
    have h := GafniTao.vinogradovKorobovDenominator_mul_le_four
      (t := 3 * Y) (q := 3) hthree100 hloglog (by norm_num) (by norm_num)
    calc
      GafniTao.vinogradovKorobovDenominator (9 * Y) =
          GafniTao.vinogradovKorobovDenominator (3 * (3 * Y)) := by
        congr 1
        ring
      _ ≤ 4 * GafniTao.vinogradovKorobovDenominator (3 * Y) := h
  have hDthree : 0 < GafniTao.vinogradovKorobovDenominator (3 * Y) :=
    GafniTao.vinogradovKorobovDenominator_pos (by simpa [Y] using hthreeBase)
  have hDnineBase : Real.exp (Real.exp 1) ≤ 9 * Y := by
    have hYpos := smoothSaddleHTFrequencyCeiling_pos y ε
    calc
      Real.exp (Real.exp 1) ≤ 3 * Y := by simpa [Y] using hthreeBase
      _ ≤ 9 * Y := by nlinarith
  have hDnine : 0 < GafniTao.vinogradovKorobovDenominator (9 * Y) :=
    GafniTao.vinogradovKorobovDenominator_pos hDnineBase
  have hshiftPos := smoothSaddleHTContourShift_pos hy ε
  have hprod : smoothSaddleHTContourShift y ε *
      GafniTao.vinogradovKorobovDenominator (3 * Y) ≤ c / 8 := by
    rw [← le_div_iff₀ hDthree]
    simpa [Y] using hwidth
  rw [le_div_iff₀ hDnine]
  calc
    2 * smoothSaddleHTContourShift y ε *
        GafniTao.vinogradovKorobovDenominator (9 * Y) ≤
      2 * smoothSaddleHTContourShift y ε *
        (4 * GafniTao.vinogradovKorobovDenominator (3 * Y)) := by
          gcongr
    _ = 8 * (smoothSaddleHTContourShift y ε *
        GafniTao.vinogradovKorobovDenominator (3 * Y)) := by ring
    _ ≤ 8 * (c / 8) := by gcongr
    _ = c := by ring

/-- A single source-scale upper bound for the high-height physical
logarithmic derivative. -/
noncomputable def smoothSaddleHTHighLogDerivativeMajorant
    (y : ℕ) (ε : ℝ) : ℝ :=
  (4 / 7 : ℝ) *
    (202 * GafniTao.sharpLandauPartialFractionConstant +
      (7 / (4 * smoothSaddleHTContourShift y ε)) *
        GafniTao.sharpLandauMassConstant) *
      Real.log (3 * smoothSaddleHTFrequencyCeiling y ε)

/-- Any ordinate between one and three HT frequency ceilings satisfies the
same sign-uniform logarithmic-derivative majorant. -/
theorem norm_riemannZeta_logDeriv_contourHeight_le_of_vK
    {c H σ R ε : ℝ} {y : ℕ}
    (hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H)
    (hHbase : Real.exp (Real.exp 1) ≤ H)
    (hy : 2 ≤ y)
    (hYbase : Real.exp (Real.exp 1) ≤
      smoothSaddleHTFrequencyCeiling y ε)
    (hWidth : 2 * smoothSaddleHTContourShift y ε ≤ c /
      GafniTao.vinogradovKorobovDenominator
        (9 * smoothSaddleHTFrequencyCeiling y ε))
    (hR8 : 8 ≤ |R|)
    (hHeight : H ≤ 3 * |R|)
    (hRupper : |R| ≤ 3 * smoothSaddleHTFrequencyCeiling y ε)
    (hSigmaIcc : σ ∈ Set.Icc (1 / 2) 2)
    (hSigma : 1 - smoothSaddleHTContourShift y ε ≤ σ) :
    ‖deriv riemannZeta ((σ : ℂ) + (R : ℂ) * Complex.I) /
        riemannZeta ((σ : ℂ) + (R : ℂ) * Complex.I)‖ ≤
      smoothSaddleHTHighLogDerivativeMajorant y ε := by
  let Y := smoothSaddleHTFrequencyCeiling y ε
  let eta := smoothSaddleHTContourShift y ε
  have heta : 0 < eta := by
    dsimp [eta]
    exact smoothSaddleHTContourShift_pos hy ε
  have hthreeRBase : Real.exp (Real.exp 1) ≤ 3 * |R| :=
    hHbase.trans hHeight
  have hnineYBase : Real.exp (Real.exp 1) ≤ 9 * Y := by
    have hYpos : 0 < Y := by
      dsimp [Y]
      exact smoothSaddleHTFrequencyCeiling_pos y ε
    change Real.exp (Real.exp 1) ≤
      9 * smoothSaddleHTFrequencyCeiling y ε
    linarith
  have hthreeRnineY : 3 * |R| ≤ 9 * Y := by
    change 3 * |R| ≤ 9 * smoothSaddleHTFrequencyCeiling y ε
    linarith
  have hmono := GafniTao.monotoneOn_vinogradovKorobovDenominator
    (le_trans (by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by norm_num)) hthreeRBase)
    (le_trans (by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by norm_num)) hnineYBase)
    hthreeRnineY
  have hDthreeR := GafniTao.vinogradovKorobovDenominator_pos hthreeRBase
  have hcNonneg : 0 ≤ c := by
    by_contra hc'
    have hcneg : c < 0 := lt_of_not_ge hc'
    have hdivneg := div_neg_of_neg_of_pos hcneg hDthreeR
    linarith [(hZeroFree hHeight).1]
  have hWidthR : 2 * eta ≤ c /
      GafniTao.vinogradovKorobovDenominator (3 * |R|) := by
    exact hWidth.trans
      (div_le_div_of_nonneg_left
        hcNonneg hDthreeR hmono)
  have hraw := norm_riemannZeta_logDeriv_abs_height_le_log_of_vK
    hZeroFree hR8 hHeight heta hWidthR hSigmaIcc hSigma
  have hlog : Real.log |R| ≤ Real.log (3 * Y) := by
    have hYpos : 0 < Y := by
      dsimp [Y]
      exact smoothSaddleHTFrequencyCeiling_pos y ε
    exact Real.log_le_log (by linarith [hR8]) hRupper
  have hcoeff : 0 ≤ (4 / 7 : ℝ) *
      (202 * GafniTao.sharpLandauPartialFractionConstant +
        (7 / (4 * eta)) * GafniTao.sharpLandauMassConstant) := by
    have hA := GafniTao.sharpLandauPartialFractionConstant_pos.le
    have hM := GafniTao.sharpLandauMassConstant_pos.le
    positivity
  exact hraw.trans (by
    unfold smoothSaddleHTHighLogDerivativeMajorant
    dsimp [eta, Y] at hcoeff hlog ⊢
    exact mul_le_mul_of_nonneg_left hlog hcoeff)

theorem smoothSaddleHT_top_physicalHeight_abs_bounds
    {y : ℕ} {ε t : ℝ}
    (ht : |t| ≤ smoothSaddleHTFrequencyCeiling y ε) :
    smoothSaddleHTFrequencyCeiling y ε ≤
        |t + smoothSaddleHTContourHeight y ε| ∧
      |t + smoothSaddleHTContourHeight y ε| ≤
        3 * smoothSaddleHTFrequencyCeiling y ε := by
  have htIcc := abs_le.mp ht
  have hYpos := smoothSaddleHTFrequencyCeiling_pos y ε
  have hnonneg : 0 ≤ t + smoothSaddleHTContourHeight y ε := by
    unfold smoothSaddleHTContourHeight
    linarith
  rw [abs_of_nonneg hnonneg]
  unfold smoothSaddleHTContourHeight
  constructor <;> linarith

theorem smoothSaddleHT_bottom_physicalHeight_abs_bounds
    {y : ℕ} {ε t : ℝ}
    (ht : |t| ≤ smoothSaddleHTFrequencyCeiling y ε) :
    smoothSaddleHTFrequencyCeiling y ε ≤
        |t - smoothSaddleHTContourHeight y ε| ∧
      |t - smoothSaddleHTContourHeight y ε| ≤
        3 * smoothSaddleHTFrequencyCeiling y ε := by
  have htIcc := abs_le.mp ht
  have hYpos := smoothSaddleHTFrequencyCeiling_pos y ε
  have hnonpos : t - smoothSaddleHTContourHeight y ε ≤ 0 := by
    unfold smoothSaddleHTContourHeight
    linarith
  rw [abs_of_nonpos hnonpos]
  unfold smoothSaddleHTContourHeight
  constructor <;> linarith

theorem smoothSaddleHT_horizontal_physicalReal_bounds
    {y : ℕ} {beta ε x : ℝ}
    (hetaHalf : smoothSaddleHTContourShift y ε ≤ 1 / 2)
    (hlogOne : 1 ≤ Real.log y)
    (hx : x ∈ Set.Icc
      (beta - smoothSaddleHTContourShift y ε)
      (smoothSaddleHTContourRight y beta)) :
    (1 - beta + x) ∈ Set.Icc (1 / 2) 2 ∧
      1 - smoothSaddleHTContourShift y ε ≤ 1 - beta + x := by
  have hlogPos : 0 < Real.log (y : ℝ) := zero_lt_one.trans_le hlogOne
  have hinv : 1 / Real.log y ≤ 1 := by
    exact (div_le_one hlogPos).2 hlogOne
  have hright : smoothSaddleHTContourRight y beta =
      beta + 1 / Real.log y := rfl
  constructor
  · constructor
    · linarith [hx.1]
    · rw [hright] at hx
      linarith [hx.2]
  · linarith [hx.1]

theorem norm_riemannZeta_logDeriv_HT_top_le_of_vK
    {c H beta ε t x : ℝ} {y : ℕ}
    (hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H)
    (hHbase : Real.exp (Real.exp 1) ≤ H)
    (hy : 2 ≤ y)
    (hYbase : Real.exp (Real.exp 1) ≤
      smoothSaddleHTFrequencyCeiling y ε)
    (hY8 : 8 ≤ smoothSaddleHTFrequencyCeiling y ε)
    (hHY : H ≤ smoothSaddleHTFrequencyCeiling y ε)
    (hWidth : 2 * smoothSaddleHTContourShift y ε ≤ c /
      GafniTao.vinogradovKorobovDenominator
        (9 * smoothSaddleHTFrequencyCeiling y ε))
    (hetaHalf : smoothSaddleHTContourShift y ε ≤ 1 / 2)
    (hlogOne : 1 ≤ Real.log y)
    (ht : |t| ≤ smoothSaddleHTFrequencyCeiling y ε)
    (hx : x ∈ Set.Icc
      (beta - smoothSaddleHTContourShift y ε)
      (smoothSaddleHTContourRight y beta)) :
    ‖deriv riemannZeta
          (((1 - beta + x : ℝ) : ℂ) +
            ((t + smoothSaddleHTContourHeight y ε : ℝ) : ℂ) * Complex.I) /
        riemannZeta
          (((1 - beta + x : ℝ) : ℂ) +
            ((t + smoothSaddleHTContourHeight y ε : ℝ) : ℂ) * Complex.I)‖ ≤
      smoothSaddleHTHighLogDerivativeMajorant y ε := by
  have hR := smoothSaddleHT_top_physicalHeight_abs_bounds ht
  have hSigma := smoothSaddleHT_horizontal_physicalReal_bounds
    hetaHalf hlogOne hx
  have hHeight : H ≤ 3 * |t + smoothSaddleHTContourHeight y ε| := by
    linarith [hHY, hR.1]
  exact norm_riemannZeta_logDeriv_contourHeight_le_of_vK
    hZeroFree hHbase hy hYbase hWidth (hY8.trans hR.1) hHeight
      hR.2 hSigma.1 hSigma.2

theorem norm_riemannZeta_logDeriv_HT_bottom_le_of_vK
    {c H beta ε t x : ℝ} {y : ℕ}
    (hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H)
    (hHbase : Real.exp (Real.exp 1) ≤ H)
    (hy : 2 ≤ y)
    (hYbase : Real.exp (Real.exp 1) ≤
      smoothSaddleHTFrequencyCeiling y ε)
    (hY8 : 8 ≤ smoothSaddleHTFrequencyCeiling y ε)
    (hHY : H ≤ smoothSaddleHTFrequencyCeiling y ε)
    (hWidth : 2 * smoothSaddleHTContourShift y ε ≤ c /
      GafniTao.vinogradovKorobovDenominator
        (9 * smoothSaddleHTFrequencyCeiling y ε))
    (hetaHalf : smoothSaddleHTContourShift y ε ≤ 1 / 2)
    (hlogOne : 1 ≤ Real.log y)
    (ht : |t| ≤ smoothSaddleHTFrequencyCeiling y ε)
    (hx : x ∈ Set.Icc
      (beta - smoothSaddleHTContourShift y ε)
      (smoothSaddleHTContourRight y beta)) :
    ‖deriv riemannZeta
          (((1 - beta + x : ℝ) : ℂ) +
            ((t - smoothSaddleHTContourHeight y ε : ℝ) : ℂ) * Complex.I) /
        riemannZeta
          (((1 - beta + x : ℝ) : ℂ) +
            ((t - smoothSaddleHTContourHeight y ε : ℝ) : ℂ) * Complex.I)‖ ≤
      smoothSaddleHTHighLogDerivativeMajorant y ε := by
  have hR := smoothSaddleHT_bottom_physicalHeight_abs_bounds ht
  have hSigma := smoothSaddleHT_horizontal_physicalReal_bounds
    hetaHalf hlogOne hx
  have hHeight : H ≤ 3 * |t - smoothSaddleHTContourHeight y ε| := by
    linarith [hHY, hR.1]
  exact norm_riemannZeta_logDeriv_contourHeight_le_of_vK
    hZeroFree hHbase hy hYbase hWidth (hY8.trans hR.1) hHeight
      hR.2 hSigma.1 hSigma.2

/-- Common high/low majorant on the physical zeta logarithmic derivative
along the complete shifted left edge. -/
noncomputable def smoothSaddleHTLeftLogDerivativeMajorant
    (y : ℕ) (ε C : ℝ) : ℝ :=
  max (C + 1 / smoothSaddleHTContourShift y ε)
    (smoothSaddleHTHighLogDerivativeMajorant y ε)

theorem norm_riemannZeta_logDeriv_HT_left_le_of_vK
    {c H ε t u C : ℝ} {y : ℕ}
    (hH : Real.exp (Real.exp 1) ≤ H) (hEightH : 8 ≤ H)
    (hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H)
    (hClow : ∀ {eta R : ℝ},
      0 < eta →
      eta ≤ c / (2 * GafniTao.vinogradovKorobovDenominator H) →
      |R| ≤ H →
      ‖deriv riemannZeta (((1 - eta : ℝ) : ℂ) +
            (R : ℂ) * Complex.I) /
          riemannZeta (((1 - eta : ℝ) : ℂ) +
            (R : ℂ) * Complex.I)‖ ≤ C + 1 / eta)
    (hy : 2 ≤ y)
    (hYbase : Real.exp (Real.exp 1) ≤
      smoothSaddleHTFrequencyCeiling y ε)
    (hWidth : 2 * smoothSaddleHTContourShift y ε ≤ c /
      GafniTao.vinogradovKorobovDenominator
        (9 * smoothSaddleHTFrequencyCeiling y ε))
    (hetaHalf : smoothSaddleHTContourShift y ε ≤ 1 / 2)
    (hetaFixed : smoothSaddleHTContourShift y ε ≤
      c / (2 * GafniTao.vinogradovKorobovDenominator H))
    (ht : |t| ≤ smoothSaddleHTFrequencyCeiling y ε)
    (hu : u ∈ Set.Icc
      (-smoothSaddleHTContourHeight y ε)
      (smoothSaddleHTContourHeight y ε)) :
    ‖deriv riemannZeta
          (((1 - smoothSaddleHTContourShift y ε : ℝ) : ℂ) +
            ((t + u : ℝ) : ℂ) * Complex.I) /
        riemannZeta
          (((1 - smoothSaddleHTContourShift y ε : ℝ) : ℂ) +
            ((t + u : ℝ) : ℂ) * Complex.I)‖ ≤
      smoothSaddleHTLeftLogDerivativeMajorant y ε C := by
  let eta := smoothSaddleHTContourShift y ε
  let R := t + u
  have heta : 0 < eta := by
    dsimp [eta]
    exact smoothSaddleHTContourShift_pos hy ε
  have hRupper : |R| ≤ 3 * smoothSaddleHTFrequencyCeiling y ε := by
    have huAbs : |u| ≤ smoothSaddleHTContourHeight y ε := abs_le.mpr hu
    calc
      |R| = |t + u| := by rfl
      _ ≤ |t| + |u| := abs_add_le _ _
      _ ≤ smoothSaddleHTFrequencyCeiling y ε +
          smoothSaddleHTContourHeight y ε := by gcongr
      _ = 3 * smoothSaddleHTFrequencyCeiling y ε := by
        unfold smoothSaddleHTContourHeight
        ring
  by_cases hRlow : |R| ≤ H
  · have hlow := hClow heta (by simpa [eta] using hetaFixed) hRlow
    exact hlow.trans (le_max_left _ _)
  · have hRhigh : H ≤ |R| := le_of_not_ge hRlow
    have hR8 : 8 ≤ |R| := hEightH.trans hRhigh
    have hHeight : H ≤ 3 * |R| := by
      have hRnonneg := abs_nonneg R
      linarith
    have hSigmaIcc : 1 - eta ∈ Set.Icc (1 / 2) 2 := by
      constructor
      · dsimp [eta] at hetaHalf ⊢
        linarith
      · linarith
    have hhigh := norm_riemannZeta_logDeriv_contourHeight_le_of_vK
      hZeroFree hH hy hYbase hWidth hR8 hHeight hRupper
      hSigmaIcc le_rfl
    exact hhigh.trans (le_max_right _ _)

end

end Tao2026
