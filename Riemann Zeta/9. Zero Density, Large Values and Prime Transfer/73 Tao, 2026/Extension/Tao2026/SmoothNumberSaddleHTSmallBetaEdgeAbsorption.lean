import Tao2026.SmoothNumberSaddleHTSmallBetaEdges
import Tao2026.SmoothNumberSaddleHTContourEdgeAbsorption

/-!
# Absorption of the negative-left HT contour edges

The horizontal terms retain the full HT height saving.  The negative-left
term has the power `y^(-eta)` and only logarithmic reciprocal-distance mass.
Together these fit the two summands of the literal equation-(3.10) error.
-/

open Filter Topology Set Complex

namespace Tao2026

noncomputable section

/-- The reciprocal-distance logarithm on the negative-left line has the
same quadratic-log bound as the positive-left specialization. -/
theorem eventually_smoothSaddleHT_smallBeta_verticalWeightLog_le_log_sq
    {ε : ℝ} (hε : 0 < ε) (hεOne : ε < 1) :
    ∀ᶠ y : ℕ in atTop,
      Real.log
          ((smoothSaddleHTContourShift y ε +
              smoothSaddleHTContourHeight y ε) /
            smoothSaddleHTContourShift y ε) ≤
        4 * (Real.log y) ^ (2 : ℕ) := by
  filter_upwards
      [eventually_smoothSaddleHT_verticalWeightLog_le_log_sq hε hεOne,
      eventually_ge_atTop (2 : ℕ)] with y hweight hy
  have heta := smoothSaddleHTContourShift_pos hy ε
  have h := hweight (2 * smoothSaddleHTContourShift y ε) le_rfl
  convert h using 1
  ring_nf

/-- Uniform scalar absorption of the complete negative-left edge majorant
into the source-faithful HT Lemma 6 error shape. -/
theorem eventually_smoothSaddleHTSmallBetaContourEdgeWeightedMajorant_le_error
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) (hεOne : ε < 1) :
    ∀ᶠ y : ℕ in atTop, ∀ beta : ℝ,
      0 < beta →
      beta ≤ 2 * smoothSaddleHTContourShift y ε →
      smoothSaddleHTSmallBetaContourEdgeWeightedMajorant y beta ε
          (smoothSaddleHTHorizontalIntegrandMajorant y beta ε)
          (smoothSaddleHTSmallBetaVerticalIntegrandNumerator y ε C) ≤
        smoothSaddleHTMangoldtError y beta ε := by
  let K := smoothSaddleHTEdgeLogConstant C
  have hK : 0 ≤ K := by
    dsimp [K]
    exact smoothSaddleHTEdgeLogConstant_nonneg hC
  have ha : 0 < ε / 2 := by positivity
  have hq : 0 < (3 : ℝ) / 2 - ε := by linarith
  have haq : ε / 2 < (3 : ℝ) / 2 - ε :=
    smoothSaddleHT_decayExponent_lt_heightExponent hεOne
  have hHorizontalAbsorb :=
    eventually_const_mul_log_rpow_mul_exp_log_rpow_le_exp_log_rpow_of_lt
      (C := 24 * K) (α := ε / 2) (β := (3 : ℝ) / 2 - ε)
      hq haq 3
  have hVerticalAbsorb :=
    eventually_const_mul_log_rpow_mul_exp_log_rpow_le_exp_log_rpow_of_lt
      (C := 16 * K) (α := 0) (β := ε / 2) ha ha 5
  have hlogTop : Tendsto (fun y : ℕ => Real.log (y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hshiftZero := tendsto_smoothSaddleHTContourShift_atTop_zero hεOne
  filter_upwards
      [eventually_smoothSaddleHTHighLogDerivativeMajorant_le_log_cube
        hC hε hεOne,
      eventually_smoothSaddleHTLeftLogDerivativeMajorant_le_log_cube
        hC hε hεOne,
      eventually_smoothSaddleHT_smallBeta_verticalWeightLog_le_log_sq
        hε hεOne,
      hshiftZero.eventually
        (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      hHorizontalAbsorb, hVerticalAbsorb,
      hlogTop.eventually (eventually_ge_atTop (1 : ℝ)),
      eventually_ge_atTop (2 : ℕ)] with
      y hhigh hleft hweight hetaHalf hHabs hVabs hL hy
  intro beta hbeta hbetaUpper
  let L : ℝ := Real.log (y : ℝ)
  let eta : ℝ := smoothSaddleHTContourShift y ε
  let Y : ℝ := smoothSaddleHTFrequencyCeiling y ε
  let T : ℝ := smoothSaddleHTContourHeight y ε
  let E : ℝ := Real.exp (L ^ (ε / 2))
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have heta : 0 < eta := by
    dsimp [eta]
    exact smoothSaddleHTContourShift_pos hy ε
  have hY : 0 < Y := by
    dsimp [Y]
    exact smoothSaddleHTFrequencyCeiling_pos y ε
  have hT : 0 < T := by
    dsimp [T]
    exact smoothSaddleHTContourHeight_pos y ε
  have hE : 0 < E := by dsimp [E]; positivity
  have hyPos : 0 < (y : ℝ) := by positivity
  have hyPow : 0 ≤ (y : ℝ) ^ beta := Real.rpow_nonneg hyPos.le _
  have hbetaOne : beta ≤ 1 := by
    linarith
  have hInvLog : 1 / L ≤ 1 := (div_le_one hLpos).2 hL
  have hLength : beta + eta + 1 / L ≤ 4 := by
    dsimp [eta, L]
    linarith
  have hHighNonneg : 0 ≤ smoothSaddleHTHighLogDerivativeMajorant y ε := by
    unfold smoothSaddleHTHighLogDerivativeMajorant
    have hlogNonneg :
        0 ≤ Real.log (3 * smoothSaddleHTFrequencyCeiling y ε) := by
      apply Real.log_nonneg
      have hYone : 1 ≤ smoothSaddleHTFrequencyCeiling y ε := by
        unfold smoothSaddleHTFrequencyCeiling
        exact Real.one_le_exp (Real.rpow_nonneg hLpos.le _)
      nlinarith
    have hA := GafniTao.sharpLandauPartialFractionConstant_pos.le
    have hM := GafniTao.sharpLandauMassConstant_pos.le
    positivity
  have hLeftNonneg : 0 ≤ smoothSaddleHTLeftLogDerivativeMajorant y ε C :=
    hHighNonneg.trans (le_max_right _ _)
  have hHorizontal : smoothSaddleHTHorizontalIntegrandMajorant y beta ε ≤
      3 * K * L ^ (3 : ℕ) * (y : ℝ) ^ beta / Y := by
    unfold smoothSaddleHTHorizontalIntegrandMajorant
    rw [rpow_smoothSaddleHTContourRight hy beta]
    have hnum :
        smoothSaddleHTHighLogDerivativeMajorant y ε *
            ((y : ℝ) ^ beta * Real.exp 1) ≤
          3 * K * L ^ (3 : ℕ) * (y : ℝ) ^ beta := by
      calc
        smoothSaddleHTHighLogDerivativeMajorant y ε *
            ((y : ℝ) ^ beta * Real.exp 1) ≤
          (K * L ^ (3 : ℕ)) * ((y : ℝ) ^ beta * Real.exp 1) := by
            gcongr
        _ ≤ (K * L ^ (3 : ℕ)) * ((y : ℝ) ^ beta * 3) := by
            gcongr
            exact Real.exp_one_lt_three.le
        _ = 3 * K * L ^ (3 : ℕ) * (y : ℝ) ^ beta := by ring
    calc
      smoothSaddleHTHighLogDerivativeMajorant y ε *
          ((y : ℝ) ^ beta * Real.exp 1) /
          smoothSaddleHTContourHeight y ε ≤
        (3 * K * L ^ (3 : ℕ) * (y : ℝ) ^ beta) /
          smoothSaddleHTContourHeight y ε :=
        div_le_div_of_nonneg_right hnum hT.le
      _ ≤ (3 * K * L ^ (3 : ℕ) * (y : ℝ) ^ beta) / Y := by
        apply div_le_div_of_nonneg_left
        · positivity
        · exact hY
        · dsimp [T, Y]
          unfold smoothSaddleHTContourHeight
          linarith
  have hVertical : smoothSaddleHTSmallBetaVerticalIntegrandNumerator y ε C ≤
      K * L ^ (3 : ℕ) * Real.exp (-2 * L ^ (ε / 2)) := by
    unfold smoothSaddleHTSmallBetaVerticalIntegrandNumerator
    rw [rpow_neg_smoothSaddleHTContourShift hy ε]
    have htail : 0 ≤ Real.exp (-2 * L ^ (ε / 2)) := Real.exp_pos _ |>.le
    calc
      smoothSaddleHTLeftLogDerivativeMajorant y ε C *
          Real.exp (-2 * (Real.log y) ^ (ε / 2)) ≤
        (K * L ^ (3 : ℕ)) * Real.exp (-2 * L ^ (ε / 2)) := by
          simpa [L] using mul_le_mul_of_nonneg_right hleft htail
      _ = K * L ^ (3 : ℕ) * Real.exp (-2 * L ^ (ε / 2)) := by rfl
  have hBracket :
      2 * smoothSaddleHTHorizontalIntegrandMajorant y beta ε *
          (beta + smoothSaddleHTContourShift y ε + 1 / Real.log y) +
        4 * smoothSaddleHTSmallBetaVerticalIntegrandNumerator y ε C *
          Real.log
            ((smoothSaddleHTContourShift y ε +
                smoothSaddleHTContourHeight y ε) /
              smoothSaddleHTContourShift y ε) ≤
      24 * K * L ^ (3 : ℕ) * (y : ℝ) ^ beta / Y +
        16 * K * L ^ (5 : ℕ) * Real.exp (-2 * L ^ (ε / 2)) := by
    have hHorizontalNonneg :
        0 ≤ smoothSaddleHTHorizontalIntegrandMajorant y beta ε := by
      unfold smoothSaddleHTHorizontalIntegrandMajorant
      positivity
    have hVerticalNonneg :
        0 ≤ smoothSaddleHTSmallBetaVerticalIntegrandNumerator y ε C := by
      unfold smoothSaddleHTSmallBetaVerticalIntegrandNumerator
      positivity
    have hweightNonneg : 0 ≤ Real.log
          ((smoothSaddleHTContourShift y ε +
              smoothSaddleHTContourHeight y ε) /
            smoothSaddleHTContourShift y ε) := by
      apply Real.log_nonneg
      rw [one_le_div heta]
      linarith [hT]
    calc
      2 * smoothSaddleHTHorizontalIntegrandMajorant y beta ε *
            (beta + smoothSaddleHTContourShift y ε + 1 / Real.log y) +
          4 * smoothSaddleHTSmallBetaVerticalIntegrandNumerator y ε C *
            Real.log
              ((smoothSaddleHTContourShift y ε +
                  smoothSaddleHTContourHeight y ε) /
                smoothSaddleHTContourShift y ε) ≤
        2 * (3 * K * L ^ (3 : ℕ) * (y : ℝ) ^ beta / Y) * 4 +
          4 * (K * L ^ (3 : ℕ) * Real.exp (-2 * L ^ (ε / 2))) *
            (4 * L ^ (2 : ℕ)) := by
              gcongr
      _ = 24 * K * L ^ (3 : ℕ) * (y : ℝ) ^ beta / Y +
          16 * K * L ^ (5 : ℕ) * Real.exp (-2 * L ^ (ε / 2)) := by ring
  have hHabs' : 24 * K * L ^ (3 : ℕ) * E ≤ Y := by
    have h := hHabs
    rw [Real.rpow_natCast] at h
    simpa [L, E, Y, smoothSaddleHTFrequencyCeiling] using h
  have hVabs' : 16 * K * L ^ (5 : ℕ) ≤ E := by
    have hExpZero : Real.exp (L ^ (0 : ℝ)) = Real.exp 1 := by
      rw [Real.rpow_zero]
    have hExpOne : 1 ≤ Real.exp (L ^ (0 : ℝ)) := by
      rw [hExpZero]
      exact Real.one_le_exp (by norm_num)
    have h := hVabs
    rw [Real.rpow_natCast] at h
    dsimp [K, L, E] at h ⊢
    have hbase : 0 ≤ 16 * smoothSaddleHTEdgeLogConstant C *
        Real.log (y : ℝ) ^ (5 : ℕ) := by positivity
    calc
      16 * smoothSaddleHTEdgeLogConstant C *
          Real.log (y : ℝ) ^ (5 : ℕ) ≤
        16 * smoothSaddleHTEdgeLogConstant C *
          Real.log (y : ℝ) ^ (5 : ℕ) *
            Real.exp (Real.log (y : ℝ) ^ (0 : ℝ)) := by
              simpa only [mul_one] using
                mul_le_mul_of_nonneg_left hExpOne hbase
      _ ≤ Real.exp (Real.log (y : ℝ) ^ (ε / 2)) := h
  have hHorizontalTarget :
      24 * K * L ^ (3 : ℕ) * (y : ℝ) ^ beta / Y ≤
        ((y : ℝ) ^ beta * Real.exp (-L ^ (ε / 2))) / beta := by
    rw [Real.exp_neg, div_le_div_iff₀ hY hbeta]
    have hcoeff : 24 * K * L ^ (3 : ℕ) * E * beta ≤ Y := by
      calc
        24 * K * L ^ (3 : ℕ) * E * beta ≤
            24 * K * L ^ (3 : ℕ) * E * 1 := by
          gcongr
        _ = 24 * K * L ^ (3 : ℕ) * E := by ring
        _ ≤ Y := hHabs'
    have hmul := mul_le_mul_of_nonneg_right hcoeff hyPow
    field_simp [ne_of_gt hE] at hmul ⊢
    nlinarith
  have hVerticalTarget :
      16 * K * L ^ (5 : ℕ) * Real.exp (-2 * L ^ (ε / 2)) ≤
        1 / beta := by
    rw [le_div_iff₀ hbeta]
    have hmul := mul_le_mul_of_nonneg_right hVabs' hbeta.le
    have hEOne : 1 ≤ E := by
      dsimp [E]
      exact Real.one_le_exp (Real.rpow_nonneg hLpos.le _)
    rw [show Real.exp (-2 * L ^ (ε / 2)) = E⁻¹ ^ 2 by
      dsimp [E]
      rw [← Real.exp_neg, ← Real.exp_nat_mul]
      congr 1
      ring]
    field_simp [ne_of_gt hE] at hmul ⊢
    nlinarith
  unfold smoothSaddleHTSmallBetaContourEdgeWeightedMajorant
  have hfactorOne : (1 / (2 * Real.pi) : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity : (0 : ℝ) < 2 * Real.pi)]
    linarith [Real.pi_gt_three]
  have hbracketNonneg : 0 ≤
      2 * smoothSaddleHTHorizontalIntegrandMajorant y beta ε *
          (beta + smoothSaddleHTContourShift y ε + 1 / Real.log y) +
        4 * smoothSaddleHTSmallBetaVerticalIntegrandNumerator y ε C *
          Real.log
            ((smoothSaddleHTContourShift y ε +
                smoothSaddleHTContourHeight y ε) /
              smoothSaddleHTContourShift y ε) := by
    have hweightNonneg : 0 ≤ Real.log
          ((smoothSaddleHTContourShift y ε +
              smoothSaddleHTContourHeight y ε) /
            smoothSaddleHTContourShift y ε) := by
      apply Real.log_nonneg
      rw [one_le_div heta]
      linarith [hT]
    exact add_nonneg
      (mul_nonneg
        (mul_nonneg (by positivity) (by
          unfold smoothSaddleHTHorizontalIntegrandMajorant
          positivity))
        (add_nonneg
          (add_nonneg hbeta.le
            (smoothSaddleHTContourShift_pos hy ε).le)
          (one_div_nonneg.mpr hLpos.le)))
      (mul_nonneg
        (mul_nonneg (by positivity) (by
          unfold smoothSaddleHTSmallBetaVerticalIntegrandNumerator
          positivity))
        hweightNonneg)
  calc
    (1 / (2 * Real.pi)) *
        (2 * smoothSaddleHTHorizontalIntegrandMajorant y beta ε *
            (beta + smoothSaddleHTContourShift y ε + 1 / Real.log y) +
          4 * smoothSaddleHTSmallBetaVerticalIntegrandNumerator y ε C *
            Real.log
              ((smoothSaddleHTContourShift y ε +
                  smoothSaddleHTContourHeight y ε) /
                smoothSaddleHTContourShift y ε)) ≤
      2 * smoothSaddleHTHorizontalIntegrandMajorant y beta ε *
            (beta + smoothSaddleHTContourShift y ε + 1 / Real.log y) +
          4 * smoothSaddleHTSmallBetaVerticalIntegrandNumerator y ε C *
            Real.log
              ((smoothSaddleHTContourShift y ε +
                  smoothSaddleHTContourHeight y ε) /
                smoothSaddleHTContourShift y ε) := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hfactorOne hbracketNonneg
    _ ≤ 24 * K * L ^ (3 : ℕ) * (y : ℝ) ^ beta / Y +
        16 * K * L ^ (5 : ℕ) * Real.exp (-2 * L ^ (ε / 2)) := hBracket
    _ ≤ ((y : ℝ) ^ beta * Real.exp (-L ^ (ε / 2))) / beta +
        1 / beta := add_le_add hHorizontalTarget hVerticalTarget
    _ = smoothSaddleHTMangoldtError y beta ε := by
      unfold smoothSaddleHTMangoldtError
      dsimp [L]
      field_simp
      ring

/-- Combining the native VK pointwise theorem with scalar absorption closes
the complete negative-left contour contribution in the small-beta branch. -/
theorem eventually_norm_smoothSaddleHTSmallBetaContourEdgeContribution_le_error_of_vK
    {c H C ε : ℝ}
    (hc : 0 < c)
    (hHbase : Real.exp (Real.exp 1) ≤ H) (hEightH : 8 ≤ H)
    (hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H)
    (hClow : ∀ {eta R : ℝ}, 0 < eta →
      eta ≤ c / (2 * GafniTao.vinogradovKorobovDenominator H) →
      |R| ≤ H →
      ‖deriv riemannZeta (((1 - eta : ℝ) : ℂ) +
            (R : ℂ) * Complex.I) /
          riemannZeta (((1 - eta : ℝ) : ℂ) +
            (R : ℂ) * Complex.I)‖ ≤ C + 1 / eta)
    (hC : 0 ≤ C) (hε : 0 < ε) (hεOne : ε < 1) :
    ∀ᶠ y : ℕ in atTop, ∀ beta t : ℝ,
      0 < beta →
      beta ≤ 2 * smoothSaddleHTContourShift y ε →
      |t| ≤ smoothSaddleHTFrequencyCeiling y ε →
      ‖smoothSaddleHTSmallBetaContourEdgeContribution y beta ε t‖ ≤
        smoothSaddleHTMangoldtError y beta ε := by
  have ha : 0 < (3 : ℝ) / 2 - ε := by linarith
  have hlogTop : Tendsto (fun y : ℕ => Real.log (y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hYTop : Tendsto
      (fun y : ℕ => smoothSaddleHTFrequencyCeiling y ε) atTop atTop := by
    simpa only [smoothSaddleHTFrequencyCeiling] using
      Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop ha).comp hlogTop)
  have hshiftZero := tendsto_smoothSaddleHTContourShift_atTop_zero hεOne
  have hD : 0 < GafniTao.vinogradovKorobovDenominator H :=
    GafniTao.vinogradovKorobovDenominator_pos hHbase
  have hfixed : 0 < c /
      (6 * GafniTao.vinogradovKorobovDenominator H) := by positivity
  have hwidthThird :=
    eventually_two_mul_smoothSaddleHTContourShift_le_vk_nine_frequency
      (c := c / 3) (by positivity) hε hεOne
  filter_upwards
      [eventually_smoothSaddleHTSmallBetaContourEdgeWeightedMajorant_le_error
        hC hε hεOne,
      hwidthThird,
      hYTop.eventually (eventually_ge_atTop (Real.exp (Real.exp 1))),
      hYTop.eventually (eventually_ge_atTop (8 : ℝ)),
      hYTop.eventually (eventually_ge_atTop H),
      hshiftZero.eventually
        (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 6)),
      hshiftZero.eventually (eventually_le_nhds hfixed),
      hlogTop.eventually (eventually_ge_atTop (1 : ℝ)),
      eventually_ge_atTop (2 : ℕ)] with
      y habsorb hwidthThird hYbase hY8 hHY hetaSix hetaFixed hlogOne hy
  intro beta t hbeta hbetaUpper ht
  let D : ℝ := GafniTao.vinogradovKorobovDenominator
    (9 * smoothSaddleHTFrequencyCeiling y ε)
  have hwidth : 6 * smoothSaddleHTContourShift y ε ≤ c / D := by
    calc
      6 * smoothSaddleHTContourShift y ε =
          3 * (2 * smoothSaddleHTContourShift y ε) := by ring
      _ ≤ 3 * ((c / 3) / D) := by
        exact mul_le_mul_of_nonneg_left
          (by simpa [D] using hwidthThird) (by norm_num)
      _ = c / D := by ring
  have hetaFixed' : 3 * smoothSaddleHTContourShift y ε ≤
      c / (2 * GafniTao.vinogradovKorobovDenominator H) := by
    calc
      3 * smoothSaddleHTContourShift y ε ≤
          3 * (c / (6 * GafniTao.vinogradovKorobovDenominator H)) := by
        gcongr
      _ = c / (2 * GafniTao.vinogradovKorobovDenominator H) := by
        ring
  have hedge :=
    norm_smoothSaddleHTSmallBetaContourEdgeContribution_le_analyticMajorant_of_vK
      hZeroFree hHbase hEightH hClow hy hYbase hY8 hHY
        (by simpa [D] using hwidth) hetaSix hetaFixed' hlogOne hbeta
          hbetaUpper ht
  exact hedge.trans (habsorb beta hbeta hbetaUpper)

/-- Complete eventual HT transform estimate in the small-beta branch.  The
origin residue, all three negative-left edges, and the Perron truncation are
simultaneously absorbed into one fixed multiple of the literal error shape. -/
theorem exists_smoothSaddleHT_eventually_smallBeta_transform_le_error
    {ε : ℝ} (hε : 0 < ε) (hεOne : ε < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ y : ℕ in atTop, ∀ beta t : ℝ,
      0 < beta →
      beta ≤ 2 * smoothSaddleHTContourShift y ε →
      |t| ≤ smoothSaddleHTFrequencyCeiling y ε →
      ‖smoothSaddleHTMangoldtTransform y beta t -
          smoothSaddleHTMangoldtMainTerm y beta t‖ ≤
        C * smoothSaddleHTMangoldtError y beta ε := by
  obtain ⟨c, H₀, K, hc, hH₀, hK, hZeroFree₀, hOrigin⟩ :=
    exists_smoothSaddleHT_eventually_originResidue_le_div_beta hε hεOne
  let H : ℝ := max H₀ 8
  have hH : Real.exp (Real.exp 1) ≤ H :=
    hH₀.trans (le_max_left _ _)
  have hEightH : 8 ≤ H := le_max_right _ _
  have hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H := by
    intro T hHT
    exact hZeroFree₀ ((le_max_left H₀ 8).trans hHT)
  obtain ⟨C₀, hC₀, hLow⟩ :=
    exists_norm_riemannZeta_logDeriv_lowHeight_leftLine_le
      hc hH hZeroFree
  obtain ⟨c₁, H₁, hc₁, hH₁, hZeroFree₁, hDecomp⟩ :=
    exists_smoothSaddleHT_native_eventually_exact_smallBeta_decomposition
      hε hεOne
  let C : ℝ := K + 2
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  have hshiftZero := tendsto_smoothSaddleHTContourShift_atTop_zero hεOne
  filter_upwards
      [hOrigin,
      eventually_norm_smoothSaddleHTSmallBetaContourEdgeContribution_le_error_of_vK
        hc hH hEightH hZeroFree hLow hC₀.le hε hεOne,
      eventually_norm_smoothSaddleHTContourTruncationError_le_mangoldtError
        hεOne,
      hDecomp,
      hshiftZero.eventually
        (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 4))] with
      y hOrigin hEdge hTrunc hDecomp hetaQuarter
  intro beta t hbeta hbetaUpper ht
  have hbetaOne : beta < 1 := by
    have hbetaHalf : beta ≤ 1 / 2 := by linarith
    linarith
  have herrorNonneg : 0 ≤ smoothSaddleHTMangoldtError y beta ε :=
    smoothSaddleHTMangoldtError_nonneg y hbeta
  have hInvLeError : 1 / beta ≤ smoothSaddleHTMangoldtError y beta ε := by
    unfold smoothSaddleHTMangoldtError
    have hX : 0 ≤ (y : ℝ) ^ beta *
        Real.exp (-(Real.log y) ^ (ε / 2)) := by positivity
    have hinv : 0 ≤ 1 / beta := one_div_nonneg.mpr hbeta.le
    calc
      1 / beta = (1 / beta) * 1 := by ring
      _ ≤ (1 / beta) *
          (1 + (y : ℝ) ^ beta *
            Real.exp (-(Real.log y) ^ (ε / 2))) := by
        exact mul_le_mul_of_nonneg_left (by linarith) hinv
  have hOrigin' :
      ‖smoothSaddleHTShiftedOriginResidue
          (smoothSaddleHTSourceExponent beta t)‖ ≤
        K * smoothSaddleHTMangoldtError y beta ε :=
    (hOrigin beta t hbeta hbetaUpper ht).trans (by
      have hmul := mul_le_mul_of_nonneg_left hInvLeError hK.le
      simpa [div_eq_mul_inv, one_div] using hmul)
  have hEdge' := hEdge beta t hbeta hbetaUpper ht
  have hTrunc' := hTrunc beta t hbeta hbetaOne
  rw [hDecomp beta t hbeta hbetaUpper ht |>.2]
  calc
    ‖smoothSaddleHTShiftedOriginResidue
          (smoothSaddleHTSourceExponent beta t) +
        smoothSaddleHTSmallBetaContourEdgeContribution y beta ε t -
          smoothSaddleHTContourTruncationError y beta ε t‖ ≤
      ‖smoothSaddleHTShiftedOriginResidue
          (smoothSaddleHTSourceExponent beta t)‖ +
        ‖smoothSaddleHTSmallBetaContourEdgeContribution y beta ε t‖ +
          ‖smoothSaddleHTContourTruncationError y beta ε t‖ := by
      simpa using (norm_add₃_le :
        ‖smoothSaddleHTShiftedOriginResidue
              (smoothSaddleHTSourceExponent beta t) +
            smoothSaddleHTSmallBetaContourEdgeContribution y beta ε t +
              (-smoothSaddleHTContourTruncationError y beta ε t)‖ ≤
          ‖smoothSaddleHTShiftedOriginResidue
              (smoothSaddleHTSourceExponent beta t)‖ +
            ‖smoothSaddleHTSmallBetaContourEdgeContribution y beta ε t‖ +
              ‖-smoothSaddleHTContourTruncationError y beta ε t‖)
    _ ≤ K * smoothSaddleHTMangoldtError y beta ε +
        smoothSaddleHTMangoldtError y beta ε +
          smoothSaddleHTMangoldtError y beta ε := by gcongr
    _ = C * smoothSaddleHTMangoldtError y beta ε := by
      dsimp [C]
      ring

/-- Complete eventual transform estimate in the complementary large-beta
branch, assembled from the already closed positive-left contour. -/
theorem eventually_smoothSaddleHT_largeBeta_transform_le_two_mul_error
    {ε : ℝ} (hε : 0 < ε) (hεOne : ε < 1) :
    ∀ᶠ y : ℕ in atTop, ∀ beta t : ℝ,
      0 < beta → beta < 1 →
      2 * smoothSaddleHTContourShift y ε ≤ beta →
      |t| ≤ smoothSaddleHTFrequencyCeiling y ε →
      ‖smoothSaddleHTMangoldtTransform y beta t -
          smoothSaddleHTMangoldtMainTerm y beta t‖ ≤
        2 * smoothSaddleHTMangoldtError y beta ε := by
  obtain ⟨c, H₀, hc, hH₀, hZeroFree₀⟩ :=
    exists_smoothSaddleHT_native_vinogradovKorobovRectangleZeroFree
  let H : ℝ := max H₀ 8
  have hH : Real.exp (Real.exp 1) ≤ H :=
    hH₀.trans (le_max_left _ _)
  have hEightH : 8 ≤ H := le_max_right _ _
  have hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H := by
    intro T hHT
    exact hZeroFree₀ ((le_max_left H₀ 8).trans hHT)
  obtain ⟨C₀, hC₀, hLow⟩ :=
    exists_norm_riemannZeta_logDeriv_lowHeight_leftLine_le
      hc hH hZeroFree
  obtain ⟨c₁, H₁, hc₁, hH₁, hZeroFree₁, hDecomp⟩ :=
    exists_smoothSaddleHT_native_eventually_exact_decomposition hε hεOne
  filter_upwards
      [eventually_norm_smoothSaddleHTContourEdgeContribution_le_target_of_vK
        hc hH hEightH hZeroFree hLow hC₀.le hε hεOne,
      eventually_norm_smoothSaddleHTContourTruncationError_le_mangoldtError
        hεOne,
      hDecomp, eventually_ge_atTop (2 : ℕ)] with y hEdge hTrunc hDecomp hy
  intro beta t hbeta hbetaOne hbetaLarge ht
  have hbetaShift : smoothSaddleHTContourShift y ε < beta := by
    have heta := smoothSaddleHTContourShift_pos hy ε
    linarith
  have hXNonneg : 0 ≤ (y : ℝ) ^ beta *
      Real.exp (-(Real.log y) ^ (ε / 2)) := by positivity
  have hXError : (y : ℝ) ^ beta *
      Real.exp (-(Real.log y) ^ (ε / 2)) ≤
        smoothSaddleHTMangoldtError y beta ε := by
    unfold smoothSaddleHTMangoldtError
    have hinv : 1 ≤ 1 / beta := by
      rw [le_div_iff₀ hbeta]
      linarith
    let X := (y : ℝ) ^ beta * Real.exp (-(Real.log y) ^ (ε / 2))
    calc
      X ≤ 1 + X := by dsimp [X]; linarith
      _ = 1 * (1 + X) := by ring
      _ ≤ (1 / beta) * (1 + X) :=
        mul_le_mul_of_nonneg_right hinv (add_nonneg (by norm_num) hXNonneg)
  rw [hDecomp beta t hbetaShift ht]
  calc
    ‖smoothSaddleHTContourEdgeContribution y beta ε t -
        smoothSaddleHTContourTruncationError y beta ε t‖ ≤
      ‖smoothSaddleHTContourEdgeContribution y beta ε t‖ +
        ‖smoothSaddleHTContourTruncationError y beta ε t‖ := norm_sub_le _ _
    _ ≤ (y : ℝ) ^ beta * Real.exp (-(Real.log y) ^ (ε / 2)) +
        smoothSaddleHTMangoldtError y beta ε :=
      add_le_add (hEdge beta t hbetaLarge ht) (hTrunc beta t hbeta hbetaOne)
    _ ≤ smoothSaddleHTMangoldtError y beta ε +
        smoothSaddleHTMangoldtError y beta ε :=
      add_le_add hXError le_rfl
    _ = 2 * smoothSaddleHTMangoldtError y beta ε := by ring

/-- Eventual source-faithful HT Lemma 6 estimate, uniform over both beta
branches. -/
theorem exists_smoothSaddleHT_eventually_transform_le_error
    {ε : ℝ} (hε : 0 < ε) (hεOne : ε < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ y : ℕ in atTop, ∀ beta t : ℝ,
      0 < beta → beta < 1 →
      |t| ≤ smoothSaddleHTFrequencyCeiling y ε →
      ‖smoothSaddleHTMangoldtTransform y beta t -
          smoothSaddleHTMangoldtMainTerm y beta t‖ ≤
        C * smoothSaddleHTMangoldtError y beta ε := by
  obtain ⟨C₀, hC₀, hSmall⟩ :=
    exists_smoothSaddleHT_eventually_smallBeta_transform_le_error hε hεOne
  let C : ℝ := max C₀ 2
  have hC : 0 < C := hC₀.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  filter_upwards
      [hSmall,
      eventually_smoothSaddleHT_largeBeta_transform_le_two_mul_error
        hε hεOne] with y hSmall hLarge
  intro beta t hbeta hbetaOne ht
  have herror : 0 ≤ smoothSaddleHTMangoldtError y beta ε :=
    smoothSaddleHTMangoldtError_nonneg y hbeta
  by_cases hbranch : beta ≤ 2 * smoothSaddleHTContourShift y ε
  · exact (hSmall beta t hbeta hbranch ht).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) herror)
  · exact (hLarge beta t hbeta hbetaOne (le_of_not_ge hbranch) ht).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) herror)

end

end Tao2026
