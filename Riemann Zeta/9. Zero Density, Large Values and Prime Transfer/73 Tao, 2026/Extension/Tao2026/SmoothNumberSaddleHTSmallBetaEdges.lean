import Tao2026.SmoothNumberSaddleHTSmallBetaHighHeight
import Tao2026.SmoothNumberSaddleHTContourEdgeAnalytic

/-!
# Weighted negative-left edges in the HT small-beta branch

The small-beta contour runs on the Perron-coordinate line `Re z = -eta`.
This file retains the Perron denominator on that line, just as the positive
left-edge argument does, and isolates the scalar majorant needed for the
remaining absorption step.
-/

open Complex MeasureTheory Set
open scoped Interval

namespace Tao2026

noncomputable section

/-- The reciprocal-distance vertical estimate is unchanged when the real
coordinate of the Perron line is negative. -/
theorem norm_VIntegral'_neg_le_of_norm_le_div_norm
    {f : ℂ → ℂ} {a T B : ℝ}
    (ha : 0 < a) (hT : 0 ≤ T) (hB : 0 ≤ B)
    (hpoint : ∀ u ∈ Set.Icc (-T) T,
      ‖f ((-a : ℂ) + (u : ℂ) * Complex.I)‖ ≤
        B / ‖(-a : ℂ) + (u : ℂ) * Complex.I‖) :
    ‖VIntegral' f (-a) (-T) T‖ ≤
      (1 / (2 * Real.pi)) *
        (4 * B * Real.log ((a + T) / a)) := by
  let g : ℂ → ℂ := fun z => f (-starRingEnd ℂ z)
  have hg := norm_VIntegral'_le_of_norm_le_div_norm
    (f := g) ha hT hB (by
      intro u hu
      have hp := hpoint u hu
      have hnorm :
          ‖((-a : ℝ) : ℂ) + (u : ℂ) * Complex.I‖ =
            ‖(a : ℂ) + (u : ℂ) * Complex.I‖ := by
        simp only [Complex.norm_def, Complex.normSq_apply]
        congr 1
        simp
      rw [show g ((a : ℂ) + (u : ℂ) * Complex.I) =
          f (((-a : ℝ) : ℂ) + (u : ℂ) * Complex.I) by
        dsimp [g]
        congr 1
        apply Complex.ext <;> simp]
      change ‖f (((-a : ℝ) : ℂ) + (u : ℂ) * Complex.I)‖ ≤
        B / ‖(a : ℂ) + (u : ℂ) * Complex.I‖
      rw [← hnorm]
      simpa only [Complex.ofReal_neg] using hp)
  simpa [VIntegral', VIntegral, g, add_comm] using hg

/-- Scalar majorant for the two horizontal edges and the negative-left
vertical edge of the small-beta rectangle. -/
noncomputable def smoothSaddleHTSmallBetaContourEdgeWeightedMajorant
    (y : ℕ) (beta ε horizontalBound verticalNumerator : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    (2 * horizontalBound *
        (beta + smoothSaddleHTContourShift y ε + 1 / Real.log y) +
      4 * verticalNumerator *
        Real.log
          ((smoothSaddleHTContourShift y ε +
              smoothSaddleHTContourHeight y ε) /
            smoothSaddleHTContourShift y ε))

/-- Pointwise bounds on the two horizontal sides and a denominator-retaining
bound on the negative-left side control the complete small-beta edge sum. -/
theorem norm_smoothSaddleHTSmallBetaContourEdgeContribution_le_weightedMajorant
    {y : ℕ} {beta ε t horizontalBound verticalNumerator : ℝ}
    (hy : 2 ≤ y) (hbeta : 0 < beta)
    (hVertical : 0 ≤ verticalNumerator)
    (hbottom : ∀ x ∈ Set.Icc
        (-smoothSaddleHTContourShift y ε)
        (smoothSaddleHTContourRight y beta),
      ‖smoothSaddleHTShiftedZetaPerronIntegrand (y : ℝ)
          (smoothSaddleHTSourceExponent beta t)
          ((x : ℂ) -
            (smoothSaddleHTContourHeight y ε : ℂ) * Complex.I)‖ ≤
        horizontalBound)
    (htop : ∀ x ∈ Set.Icc
        (-smoothSaddleHTContourShift y ε)
        (smoothSaddleHTContourRight y beta),
      ‖smoothSaddleHTShiftedZetaPerronIntegrand (y : ℝ)
          (smoothSaddleHTSourceExponent beta t)
          ((x : ℂ) +
            (smoothSaddleHTContourHeight y ε : ℂ) * Complex.I)‖ ≤
        horizontalBound)
    (hleft : ∀ u ∈ Set.Icc
        (-smoothSaddleHTContourHeight y ε)
        (smoothSaddleHTContourHeight y ε),
      ‖smoothSaddleHTShiftedZetaPerronIntegrand (y : ℝ)
          (smoothSaddleHTSourceExponent beta t)
          ((-smoothSaddleHTContourShift y ε : ℂ) +
            (u : ℂ) * Complex.I)‖ ≤
        verticalNumerator /
          ‖(-smoothSaddleHTContourShift y ε : ℂ) +
            (u : ℂ) * Complex.I‖) :
    ‖smoothSaddleHTSmallBetaContourEdgeContribution y beta ε t‖ ≤
      smoothSaddleHTSmallBetaContourEdgeWeightedMajorant y beta ε
        horizontalBound verticalNumerator := by
  let eta : ℝ := smoothSaddleHTContourShift y ε
  let left : ℝ := -eta
  let right : ℝ := smoothSaddleHTContourRight y beta
  let T : ℝ := smoothSaddleHTContourHeight y ε
  let F : ℂ → ℂ := smoothSaddleHTShiftedZetaPerronIntegrand (y : ℝ)
    (smoothSaddleHTSourceExponent beta t)
  have heta : 0 < eta := by
    dsimp [eta]
    exact smoothSaddleHTContourShift_pos hy ε
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlr : left ≤ right := by
    have hinv : 0 < 1 / Real.log (y : ℝ) := one_div_pos.mpr hlog
    dsimp [left, right, eta, smoothSaddleHTContourRight]
    linarith
  have hT : 0 ≤ T := (smoothSaddleHTContourHeight_pos y ε).le
  have hbottom' : ‖HIntegral' F left right (-T)‖ ≤
      (1 / (2 * Real.pi)) * horizontalBound * (right - left) := by
    apply norm_HIntegral'_le_of_norm_le_const hlr
    intro x hx
    simpa [F, T, left, right, eta, sub_eq_add_neg] using
      hbottom x (by simpa [left, right, eta] using hx)
  have htop' : ‖HIntegral' F left right T‖ ≤
      (1 / (2 * Real.pi)) * horizontalBound * (right - left) := by
    apply norm_HIntegral'_le_of_norm_le_const hlr
    intro x hx
    exact htop x (by simpa [F, T, left, right, eta] using hx)
  have hleft' : ‖VIntegral' F left (-T) T‖ ≤
      (1 / (2 * Real.pi)) *
        (4 * verticalNumerator * Real.log ((eta + T) / eta)) := by
    have h := norm_VIntegral'_neg_le_of_norm_le_div_norm
      (f := F) heta hT hVertical (by
        intro u hu
        simpa [F, eta, T] using hleft u (by simpa [T] using hu))
    simpa [left] using h
  unfold smoothSaddleHTSmallBetaContourEdgeContribution
  change ‖-HIntegral' F left right (-T) + HIntegral' F left right T +
      VIntegral' F left (-T) T‖ ≤ _
  calc
    ‖-HIntegral' F left right (-T) + HIntegral' F left right T +
        VIntegral' F left (-T) T‖ ≤
      ‖HIntegral' F left right (-T)‖ +
        ‖HIntegral' F left right T‖ +
          ‖VIntegral' F left (-T) T‖ := by
            simpa using (norm_add₃_le :
              ‖-HIntegral' F left right (-T) + HIntegral' F left right T +
                  VIntegral' F left (-T) T‖ ≤
                ‖-HIntegral' F left right (-T)‖ +
                  ‖HIntegral' F left right T‖ +
                    ‖VIntegral' F left (-T) T‖)
    _ ≤ (1 / (2 * Real.pi)) * horizontalBound * (right - left) +
        (1 / (2 * Real.pi)) * horizontalBound * (right - left) +
          (1 / (2 * Real.pi)) *
            (4 * verticalNumerator * Real.log ((eta + T) / eta)) := by
              gcongr
    _ = smoothSaddleHTSmallBetaContourEdgeWeightedMajorant y beta ε
        horizontalBound verticalNumerator := by
      have hlength : right - left =
          beta + smoothSaddleHTContourShift y ε + 1 / Real.log y := by
        dsimp [right, left, eta, smoothSaddleHTContourRight]
        ring
      rw [hlength]
      simp only [eta, T, smoothSaddleHTSmallBetaContourEdgeWeightedMajorant]
      ring

/-- Numerator retained over the Perron denominator on the negative-left
small-beta edge. -/
noncomputable def smoothSaddleHTSmallBetaVerticalIntegrandNumerator
    (y : ℕ) (ε C : ℝ) : ℝ :=
  smoothSaddleHTLeftLogDerivativeMajorant y ε C *
    (y : ℝ) ^ (-smoothSaddleHTContourShift y ε)

/-- A physical logarithmic-derivative bound on the negative-left line
transfers to the shifted Perron integrand without discarding its denominator. -/
theorem norm_smoothSaddleHTShiftedZetaPerronIntegrand_negativeLeft_le
    {y : ℕ} {beta ε t u L : ℝ}
    (hy : 2 ≤ y) (hbeta : 0 < beta)
    (hsur : GafniTao.sharpZetaSurrogate
      (smoothSaddleHTSourceExponent beta t +
        ((-smoothSaddleHTContourShift y ε : ℂ) +
          (u : ℂ) * Complex.I)) ≠ 0)
    (hlog : ‖deriv riemannZeta
          (((1 - beta - smoothSaddleHTContourShift y ε : ℝ) : ℂ) +
            ((t + u : ℝ) : ℂ) * Complex.I) /
        riemannZeta
          (((1 - beta - smoothSaddleHTContourShift y ε : ℝ) : ℂ) +
            ((t + u : ℝ) : ℂ) * Complex.I)‖ ≤ L) :
    ‖smoothSaddleHTShiftedZetaPerronIntegrand (y : ℝ)
        (smoothSaddleHTSourceExponent beta t)
        ((-smoothSaddleHTContourShift y ε : ℂ) +
          (u : ℂ) * Complex.I)‖ ≤
      L * (y : ℝ) ^ (-smoothSaddleHTContourShift y ε) /
        ‖(-smoothSaddleHTContourShift y ε : ℂ) +
          (u : ℂ) * Complex.I‖ := by
  let eta : ℝ := smoothSaddleHTContourShift y ε
  let z : ℂ := (-eta : ℂ) + (u : ℂ) * Complex.I
  let w : ℂ := smoothSaddleHTSourceExponent beta t + z
  have heta : 0 < eta := by
    dsimp [eta]
    exact smoothSaddleHTContourShift_pos hy ε
  have hz0 : z ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    simp [z] at hre
    linarith
  have hw1 : w ≠ 1 := by
    intro hw
    have hre := congrArg Complex.re hw
    simp [w, z, eta, smoothSaddleHTSourceExponent] at hre
    linarith
  have hzeta : riemannZeta w ≠ 0 := by
    intro hzeta
    exact hsur ((GafniTao.sharpZetaSurrogate_eq_zero_iff hw1).2
      (by simpa [w, z, eta] using hzeta))
  have hw : w =
      (((1 - beta - eta : ℝ) : ℂ) +
        ((t + u : ℝ) : ℂ) * Complex.I) := by
    apply Complex.ext
    · simp [w, z, eta, smoothSaddleHTSourceExponent]
      ring
    · simp [w, z, eta, smoothSaddleHTSourceExponent]
  have hraw := norm_smoothSaddleHTShiftedZetaPerronIntegrand_le
    (y := (y : ℝ)) (s := smoothSaddleHTSourceExponent beta t) (z := z)
    (by positivity) hz0 (by simpa [w] using hw1)
    (by simpa [w] using hzeta) (by simpa [w, hw, eta] using hlog)
  simpa [z, eta] using hraw

/-- Spending three copies of the HT shift covers every physical real part
on the small-beta rectangle while retaining the established high-height
majorant. -/
theorem norm_riemannZeta_logDeriv_threeShift_contourHeight_le_of_vK
    {c H sigma R ε : ℝ} {y : ℕ}
    (hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H)
    (hHbase : Real.exp (Real.exp 1) ≤ H)
    (hy : 2 ≤ y)
    (hYbase : Real.exp (Real.exp 1) ≤
      smoothSaddleHTFrequencyCeiling y ε)
    (hWidth : 6 * smoothSaddleHTContourShift y ε ≤ c /
      GafniTao.vinogradovKorobovDenominator
        (9 * smoothSaddleHTFrequencyCeiling y ε))
    (hR8 : 8 ≤ |R|) (hHeight : H ≤ 3 * |R|)
    (hRupper : |R| ≤ 3 * smoothSaddleHTFrequencyCeiling y ε)
    (hSigmaIcc : sigma ∈ Set.Icc (1 / 2) 2)
    (hSigma : 1 - 3 * smoothSaddleHTContourShift y ε ≤ sigma) :
    ‖deriv riemannZeta ((sigma : ℂ) + (R : ℂ) * Complex.I) /
        riemannZeta ((sigma : ℂ) + (R : ℂ) * Complex.I)‖ ≤
      smoothSaddleHTHighLogDerivativeMajorant y ε := by
  let Y : ℝ := smoothSaddleHTFrequencyCeiling y ε
  let eta : ℝ := smoothSaddleHTContourShift y ε
  have heta : 0 < eta := by
    dsimp [eta]
    exact smoothSaddleHTContourShift_pos hy ε
  have hthreeRBase : Real.exp (Real.exp 1) ≤ 3 * |R| :=
    hHbase.trans hHeight
  have hnineYBase : Real.exp (Real.exp 1) ≤ 9 * Y := by
    have hYpos : 0 < Y := by
      dsimp [Y]
      exact smoothSaddleHTFrequencyCeiling_pos y ε
    dsimp [Y]
    linarith
  have hthreeRnineY : 3 * |R| ≤ 9 * Y := by
    dsimp [Y]
    linarith
  have hmono := GafniTao.monotoneOn_vinogradovKorobovDenominator
    (le_trans (by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by norm_num)) hthreeRBase)
    (le_trans (by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by norm_num)) hnineYBase)
    hthreeRnineY
  have hDthreeR :=
    GafniTao.vinogradovKorobovDenominator_pos hthreeRBase
  have hcNonneg : 0 ≤ c := by
    by_contra hc'
    have hcneg : c < 0 := lt_of_not_ge hc'
    have hdivneg := div_neg_of_neg_of_pos hcneg hDthreeR
    linarith [(hZeroFree hHeight).1]
  have hWidthR : 2 * (3 * eta) ≤ c /
      GafniTao.vinogradovKorobovDenominator (3 * |R|) := by
    have hwidthNine : 6 * eta ≤ c /
        GafniTao.vinogradovKorobovDenominator (9 * Y) := by
      simpa [eta, Y] using hWidth
    have hraw : 6 * eta ≤ c /
        GafniTao.vinogradovKorobovDenominator (3 * |R|) :=
      hwidthNine.trans
        (div_le_div_of_nonneg_left hcNonneg hDthreeR hmono)
    nlinarith
  have hraw := norm_riemannZeta_logDeriv_abs_height_le_log_of_vK
    hZeroFree hR8 hHeight (by positivity : 0 < 3 * eta) hWidthR
      hSigmaIcc hSigma
  have hYpos : 0 < Y := by
    dsimp [Y]
    exact smoothSaddleHTFrequencyCeiling_pos y ε
  have hlog : Real.log |R| ≤ Real.log (3 * Y) :=
    Real.log_le_log (by linarith [hR8]) hRupper
  have hfrac : 7 / (4 * (3 * eta)) ≤ 7 / (4 * eta) := by
    apply div_le_div_of_nonneg_left (by norm_num)
    · positivity
    · nlinarith
  have hA := GafniTao.sharpLandauPartialFractionConstant_pos.le
  have hM := GafniTao.sharpLandauMassConstant_pos.le
  have hlogNonneg : 0 ≤ Real.log |R| :=
    Real.log_nonneg (by linarith [hR8])
  calc
    ‖deriv riemannZeta ((sigma : ℂ) + (R : ℂ) * Complex.I) /
        riemannZeta ((sigma : ℂ) + (R : ℂ) * Complex.I)‖ ≤
      (4 / 7 : ℝ) *
        (202 * GafniTao.sharpLandauPartialFractionConstant +
          (7 / (4 * (3 * eta))) * GafniTao.sharpLandauMassConstant) *
            Real.log |R| := hraw
    _ ≤ (4 / 7 : ℝ) *
        (202 * GafniTao.sharpLandauPartialFractionConstant +
          (7 / (4 * eta)) * GafniTao.sharpLandauMassConstant) *
            Real.log |R| := by gcongr
    _ ≤ (4 / 7 : ℝ) *
        (202 * GafniTao.sharpLandauPartialFractionConstant +
          (7 / (4 * eta)) * GafniTao.sharpLandauMassConstant) *
            Real.log (3 * Y) := by
      gcongr
    _ = smoothSaddleHTHighLogDerivativeMajorant y ε := by
      rfl

/-- Physical real-part geometry on a small-beta horizontal edge. -/
theorem smoothSaddleHT_smallBeta_horizontal_physicalReal_bounds
    {y : ℕ} {beta ε x : ℝ}
    (hetaSix : smoothSaddleHTContourShift y ε ≤ 1 / 6)
    (hlogOne : 1 ≤ Real.log y)
    (hbetaUpper : beta ≤ 2 * smoothSaddleHTContourShift y ε)
    (hx : x ∈ Set.Icc (-smoothSaddleHTContourShift y ε)
      (smoothSaddleHTContourRight y beta)) :
    (1 - beta + x) ∈ Set.Icc (1 / 2) 2 ∧
      1 - 3 * smoothSaddleHTContourShift y ε ≤ 1 - beta + x := by
  have hlogPos : 0 < Real.log (y : ℝ) := zero_lt_one.trans_le hlogOne
  have hinv : 1 / Real.log y ≤ 1 := (div_le_one hlogPos).2 hlogOne
  constructor
  · constructor
    · linarith [hx.1]
    · have hxright : x ≤ beta + 1 / Real.log y := by
        simpa [smoothSaddleHTContourRight] using hx.2
      linarith
  · linarith [hx.1]

set_option linter.unnecessarySeqFocus false in
/-- Uniform high/low physical logarithmic-derivative bound on the complete
negative-left edge in the small-beta branch. -/
theorem norm_riemannZeta_logDeriv_HT_smallBeta_negativeLeft_le_of_vK
    {c H beta ε t u C : ℝ} {y : ℕ}
    (hH : Real.exp (Real.exp 1) ≤ H) (hEightH : 8 ≤ H)
    (hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H)
    (hClow : ∀ {eta R : ℝ}, 0 < eta →
      eta ≤ c / (2 * GafniTao.vinogradovKorobovDenominator H) →
      |R| ≤ H →
      ‖deriv riemannZeta (((1 - eta : ℝ) : ℂ) +
            (R : ℂ) * Complex.I) /
          riemannZeta (((1 - eta : ℝ) : ℂ) +
            (R : ℂ) * Complex.I)‖ ≤ C + 1 / eta)
    (hy : 2 ≤ y)
    (hYbase : Real.exp (Real.exp 1) ≤
      smoothSaddleHTFrequencyCeiling y ε)
    (hWidth : 6 * smoothSaddleHTContourShift y ε ≤ c /
      GafniTao.vinogradovKorobovDenominator
        (9 * smoothSaddleHTFrequencyCeiling y ε))
    (hetaSix : smoothSaddleHTContourShift y ε ≤ 1 / 6)
    (hetaFixed : 3 * smoothSaddleHTContourShift y ε ≤
      c / (2 * GafniTao.vinogradovKorobovDenominator H))
    (hbeta : 0 < beta)
    (hbetaUpper : beta ≤ 2 * smoothSaddleHTContourShift y ε)
    (ht : |t| ≤ smoothSaddleHTFrequencyCeiling y ε)
    (hu : u ∈ Set.Icc (-smoothSaddleHTContourHeight y ε)
      (smoothSaddleHTContourHeight y ε)) :
    ‖deriv riemannZeta
          (((1 - beta - smoothSaddleHTContourShift y ε : ℝ) : ℂ) +
            ((t + u : ℝ) : ℂ) * Complex.I) /
        riemannZeta
          (((1 - beta - smoothSaddleHTContourShift y ε : ℝ) : ℂ) +
            ((t + u : ℝ) : ℂ) * Complex.I)‖ ≤
      smoothSaddleHTLeftLogDerivativeMajorant y ε C := by
  let eta : ℝ := smoothSaddleHTContourShift y ε
  let delta : ℝ := beta + eta
  let R : ℝ := t + u
  have heta : 0 < eta := by
    dsimp [eta]
    exact smoothSaddleHTContourShift_pos hy ε
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  have hdeltaUpper : delta ≤ 3 * eta := by
    dsimp [delta, eta] at hbetaUpper ⊢
    linarith
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
  · have hlow := hClow hdelta (hdeltaUpper.trans (by simpa [eta] using hetaFixed)) hRlow
    have hinv : 1 / delta ≤ 1 / eta :=
      one_div_le_one_div_of_le heta (by dsimp [delta]; linarith)
    have hlow' : C + 1 / delta ≤ C + 1 / eta := by linarith
    unfold smoothSaddleHTLeftLogDerivativeMajorant
    calc
      ‖deriv riemannZeta
            (((1 - beta - smoothSaddleHTContourShift y ε : ℝ) : ℂ) +
              ((t + u : ℝ) : ℂ) * Complex.I) /
          riemannZeta
            (((1 - beta - smoothSaddleHTContourShift y ε : ℝ) : ℂ) +
              ((t + u : ℝ) : ℂ) * Complex.I)‖ ≤ C + 1 / delta := by
        convert hlow using 1 <;> simp [delta, eta, R] <;> ring_nf
      _ ≤ C + 1 / eta := hlow'
      _ ≤ max (C + 1 / smoothSaddleHTContourShift y ε)
          (smoothSaddleHTHighLogDerivativeMajorant y ε) := by
        change C + 1 / eta ≤ max (C + 1 / eta)
          (smoothSaddleHTHighLogDerivativeMajorant y ε)
        exact le_max_left _ _
  · have hRhigh : H ≤ |R| := le_of_not_ge hRlow
    have hR8 : 8 ≤ |R| := hEightH.trans hRhigh
    have hHeight : H ≤ 3 * |R| := by
      nlinarith [abs_nonneg R]
    have hSigmaIcc : 1 - delta ∈ Set.Icc (1 / 2) 2 := by
      constructor
      · have hthree : 3 * eta ≤ 1 / 2 := by
          dsimp [eta] at hetaSix ⊢
          linarith
        linarith
      · linarith
    have hhigh := norm_riemannZeta_logDeriv_threeShift_contourHeight_le_of_vK
      hZeroFree hH hy hYbase hWidth hR8 hHeight hRupper hSigmaIcc
        (by linarith)
    unfold smoothSaddleHTLeftLogDerivativeMajorant
    calc
      ‖deriv riemannZeta
            (((1 - beta - smoothSaddleHTContourShift y ε : ℝ) : ℂ) +
              ((t + u : ℝ) : ℂ) * Complex.I) /
          riemannZeta
            (((1 - beta - smoothSaddleHTContourShift y ε : ℝ) : ℂ) +
              ((t + u : ℝ) : ℂ) * Complex.I)‖ ≤
          smoothSaddleHTHighLogDerivativeMajorant y ε := by
        convert hhigh using 1 <;> simp [delta, eta, R] <;> ring_nf
      _ ≤ max (C + 1 / smoothSaddleHTContourShift y ε)
          (smoothSaddleHTHighLogDerivativeMajorant y ε) :=
        le_max_right _ _

/-- The three physical logarithmic-derivative bounds and a zero-free
rectangle discharge the weighted negative-left edge estimate. -/
theorem norm_smoothSaddleHTSmallBetaContourEdgeContribution_le_analyticMajorant
    {y : ℕ} {beta ε t C : ℝ}
    (hy : 2 ≤ y) (hbeta : 0 < beta)
    (ht : |t| ≤ smoothSaddleHTFrequencyCeiling y ε)
    (hHighNonneg : 0 ≤ smoothSaddleHTHighLogDerivativeMajorant y ε)
    (hLeftNonneg : 0 ≤ smoothSaddleHTLeftLogDerivativeMajorant y ε C)
    (hsur : ∀ z ∈ Rectangle
        ((-smoothSaddleHTContourShift y ε : ℂ) -
          (smoothSaddleHTContourHeight y ε : ℂ) * Complex.I)
        (((smoothSaddleHTContourRight y beta : ℝ) : ℂ) +
          (smoothSaddleHTContourHeight y ε : ℂ) * Complex.I),
      GafniTao.sharpZetaSurrogate
        (smoothSaddleHTSourceExponent beta t + z) ≠ 0)
    (htopLog : ∀ x ∈ Set.Icc (-smoothSaddleHTContourShift y ε)
        (smoothSaddleHTContourRight y beta),
      ‖deriv riemannZeta
            (((1 - beta + x : ℝ) : ℂ) +
              ((t + smoothSaddleHTContourHeight y ε : ℝ) : ℂ) * Complex.I) /
          riemannZeta
            (((1 - beta + x : ℝ) : ℂ) +
              ((t + smoothSaddleHTContourHeight y ε : ℝ) : ℂ) * Complex.I)‖ ≤
        smoothSaddleHTHighLogDerivativeMajorant y ε)
    (hbottomLog : ∀ x ∈ Set.Icc (-smoothSaddleHTContourShift y ε)
        (smoothSaddleHTContourRight y beta),
      ‖deriv riemannZeta
            (((1 - beta + x : ℝ) : ℂ) +
              ((t - smoothSaddleHTContourHeight y ε : ℝ) : ℂ) * Complex.I) /
          riemannZeta
            (((1 - beta + x : ℝ) : ℂ) +
              ((t - smoothSaddleHTContourHeight y ε : ℝ) : ℂ) * Complex.I)‖ ≤
        smoothSaddleHTHighLogDerivativeMajorant y ε)
    (hleftLog : ∀ u ∈ Set.Icc (-smoothSaddleHTContourHeight y ε)
        (smoothSaddleHTContourHeight y ε),
      ‖deriv riemannZeta
            (((1 - beta - smoothSaddleHTContourShift y ε : ℝ) : ℂ) +
              ((t + u : ℝ) : ℂ) * Complex.I) /
          riemannZeta
            (((1 - beta - smoothSaddleHTContourShift y ε : ℝ) : ℂ) +
              ((t + u : ℝ) : ℂ) * Complex.I)‖ ≤
        smoothSaddleHTLeftLogDerivativeMajorant y ε C) :
    ‖smoothSaddleHTSmallBetaContourEdgeContribution y beta ε t‖ ≤
      smoothSaddleHTSmallBetaContourEdgeWeightedMajorant y beta ε
        (smoothSaddleHTHorizontalIntegrandMajorant y beta ε)
        (smoothSaddleHTSmallBetaVerticalIntegrandNumerator y ε C) := by
  let eta : ℝ := smoothSaddleHTContourShift y ε
  let T : ℝ := smoothSaddleHTContourHeight y ε
  let right : ℝ := smoothSaddleHTContourRight y beta
  have heta : 0 < eta := by
    dsimp [eta]
    exact smoothSaddleHTContourShift_pos hy ε
  have hT : 0 < T := by
    dsimp [T]
    exact smoothSaddleHTContourHeight_pos y ε
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlr : -eta ≤ right := by
    dsimp [eta, right, smoothSaddleHTContourRight]
    have hinv : 0 < 1 / Real.log (y : ℝ) := one_div_pos.mpr hlog
    linarith
  have hTorder : -T ≤ T := by linarith
  have htopPhysical := smoothSaddleHT_top_physicalHeight_abs_bounds ht
  have hbottomPhysical := smoothSaddleHT_bottom_physicalHeight_abs_bounds ht
  have hYpos := smoothSaddleHTFrequencyCeiling_pos y ε
  apply norm_smoothSaddleHTSmallBetaContourEdgeContribution_le_weightedMajorant
    hy hbeta
  · unfold smoothSaddleHTSmallBetaVerticalIntegrandNumerator
    exact mul_nonneg hLeftNonneg (Real.rpow_nonneg (by positivity) _)
  · intro x hx
    have hsurPoint : GafniTao.sharpZetaSurrogate
        (smoothSaddleHTSourceExponent beta t +
          ((x : ℂ) - (T : ℂ) * Complex.I)) ≠ 0 := by
      apply hsur
      change
        ((x : ℂ) - (T : ℂ) * Complex.I).re ∈ Set.uIcc
            ((-smoothSaddleHTContourShift y ε : ℂ) -
              (smoothSaddleHTContourHeight y ε : ℂ) * Complex.I).re
            (((smoothSaddleHTContourRight y beta : ℝ) : ℂ) +
              (smoothSaddleHTContourHeight y ε : ℂ) * Complex.I).re ∧
          ((x : ℂ) - (T : ℂ) * Complex.I).im ∈ Set.uIcc
            ((-smoothSaddleHTContourShift y ε : ℂ) -
              (smoothSaddleHTContourHeight y ε : ℂ) * Complex.I).im
            (((smoothSaddleHTContourRight y beta : ℝ) : ℂ) +
              (smoothSaddleHTContourHeight y ε : ℂ) * Complex.I).im
      constructor
      · simpa [Set.uIcc_of_le hlr, eta, right] using hx
      · have : -T ∈ Set.uIcc (-T) T := by
          rw [Set.uIcc_of_le hTorder]
          exact ⟨le_rfl, hTorder⟩
        convert this using 1 <;> simp [T]
    have hpoint := norm_smoothSaddleHTShiftedZetaPerronIntegrand_horizontal_le
      hy hx.2 (v := -T)
      (abs_pos.mpr (neg_ne_zero.mpr (ne_of_gt hT)))
      (by simpa [T, sub_eq_add_neg] using
        (show 0 < |t - smoothSaddleHTContourHeight y ε| from
          hYpos.trans_le hbottomPhysical.1))
      (by simpa [T, sub_eq_add_neg] using hsurPoint)
      (by simpa [T, sub_eq_add_neg] using hbottomLog x hx)
      hHighNonneg
    simpa [smoothSaddleHTHorizontalIntegrandMajorant, T, abs_of_pos hT]
      using hpoint
  · intro x hx
    have hsurPoint : GafniTao.sharpZetaSurrogate
        (smoothSaddleHTSourceExponent beta t +
          ((x : ℂ) + (T : ℂ) * Complex.I)) ≠ 0 := by
      apply hsur
      change
        ((x : ℂ) + (T : ℂ) * Complex.I).re ∈ Set.uIcc
            ((-smoothSaddleHTContourShift y ε : ℂ) -
              (smoothSaddleHTContourHeight y ε : ℂ) * Complex.I).re
            (((smoothSaddleHTContourRight y beta : ℝ) : ℂ) +
              (smoothSaddleHTContourHeight y ε : ℂ) * Complex.I).re ∧
          ((x : ℂ) + (T : ℂ) * Complex.I).im ∈ Set.uIcc
            ((-smoothSaddleHTContourShift y ε : ℂ) -
              (smoothSaddleHTContourHeight y ε : ℂ) * Complex.I).im
            (((smoothSaddleHTContourRight y beta : ℝ) : ℂ) +
              (smoothSaddleHTContourHeight y ε : ℂ) * Complex.I).im
      constructor
      · simpa [Set.uIcc_of_le hlr, eta, right] using hx
      · have : T ∈ Set.uIcc (-T) T := by
          rw [Set.uIcc_of_le hTorder]
          exact ⟨hTorder, le_rfl⟩
        convert this using 1 <;> simp [T]
    have hpoint := norm_smoothSaddleHTShiftedZetaPerronIntegrand_horizontal_le
      hy hx.2 (v := T) (abs_pos.mpr (ne_of_gt hT))
      (by simpa [T] using
        (show 0 < |t + smoothSaddleHTContourHeight y ε| from
          hYpos.trans_le htopPhysical.1))
      (by simpa [T] using hsurPoint) (by simpa [T] using htopLog x hx)
      hHighNonneg
    simpa [smoothSaddleHTHorizontalIntegrandMajorant, T, abs_of_pos hT]
      using hpoint
  · intro u hu
    have hsurPoint : GafniTao.sharpZetaSurrogate
        (smoothSaddleHTSourceExponent beta t +
          ((-eta : ℂ) + (u : ℂ) * Complex.I)) ≠ 0 := by
      apply hsur
      change
        ((-eta : ℂ) + (u : ℂ) * Complex.I).re ∈ Set.uIcc
            ((-smoothSaddleHTContourShift y ε : ℂ) -
              (smoothSaddleHTContourHeight y ε : ℂ) * Complex.I).re
            (((smoothSaddleHTContourRight y beta : ℝ) : ℂ) +
              (smoothSaddleHTContourHeight y ε : ℂ) * Complex.I).re ∧
          ((-eta : ℂ) + (u : ℂ) * Complex.I).im ∈ Set.uIcc
            ((-smoothSaddleHTContourShift y ε : ℂ) -
              (smoothSaddleHTContourHeight y ε : ℂ) * Complex.I).im
            (((smoothSaddleHTContourRight y beta : ℝ) : ℂ) +
              (smoothSaddleHTContourHeight y ε : ℂ) * Complex.I).im
      constructor
      · have : -eta ∈ Set.uIcc (-eta) right := by
          rw [Set.uIcc_of_le hlr]
          exact ⟨le_rfl, hlr⟩
        convert this using 1 <;> simp [eta, right]
      · simpa [Set.uIcc_of_le hTorder, T] using hu
    have hpoint := norm_smoothSaddleHTShiftedZetaPerronIntegrand_negativeLeft_le
      hy hbeta (by simpa [eta] using hsurPoint) (hleftLog u hu)
    simpa [smoothSaddleHTSmallBetaVerticalIntegrandNumerator, eta] using hpoint

/-- Native VK and compact low-height inputs specialize every hypothesis of
the analytic negative-left edge theorem. -/
theorem norm_smoothSaddleHTSmallBetaContourEdgeContribution_le_analyticMajorant_of_vK
    {c H beta ε t C : ℝ} {y : ℕ}
    (hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H)
    (hHbase : Real.exp (Real.exp 1) ≤ H) (hEightH : 8 ≤ H)
    (hClow : ∀ {eta R : ℝ}, 0 < eta →
      eta ≤ c / (2 * GafniTao.vinogradovKorobovDenominator H) →
      |R| ≤ H →
      ‖deriv riemannZeta (((1 - eta : ℝ) : ℂ) +
            (R : ℂ) * Complex.I) /
          riemannZeta (((1 - eta : ℝ) : ℂ) +
            (R : ℂ) * Complex.I)‖ ≤ C + 1 / eta)
    (hy : 2 ≤ y)
    (hYbase : Real.exp (Real.exp 1) ≤
      smoothSaddleHTFrequencyCeiling y ε)
    (hY8 : 8 ≤ smoothSaddleHTFrequencyCeiling y ε)
    (hHY : H ≤ smoothSaddleHTFrequencyCeiling y ε)
    (hWidth : 6 * smoothSaddleHTContourShift y ε ≤ c /
      GafniTao.vinogradovKorobovDenominator
        (9 * smoothSaddleHTFrequencyCeiling y ε))
    (hetaSix : smoothSaddleHTContourShift y ε ≤ 1 / 6)
    (hetaFixed : 3 * smoothSaddleHTContourShift y ε ≤
      c / (2 * GafniTao.vinogradovKorobovDenominator H))
    (hlogOne : 1 ≤ Real.log y)
    (hbeta : 0 < beta)
    (hbetaUpper : beta ≤ 2 * smoothSaddleHTContourShift y ε)
    (ht : |t| ≤ smoothSaddleHTFrequencyCeiling y ε) :
    ‖smoothSaddleHTSmallBetaContourEdgeContribution y beta ε t‖ ≤
      smoothSaddleHTSmallBetaContourEdgeWeightedMajorant y beta ε
        (smoothSaddleHTHorizontalIntegrandMajorant y beta ε)
        (smoothSaddleHTSmallBetaVerticalIntegrandNumerator y ε C) := by
  let eta : ℝ := smoothSaddleHTContourShift y ε
  let Y : ℝ := smoothSaddleHTFrequencyCeiling y ε
  let T : ℝ := smoothSaddleHTContourHeight y ε
  let A : ℝ := |t| + T
  let B : ℝ := 9 * Y
  have heta : 0 < eta := by
    dsimp [eta]
    exact smoothSaddleHTContourShift_pos hy ε
  have hT : 0 < T := by
    dsimp [T]
    exact smoothSaddleHTContourHeight_pos y ε
  have hAheight : H ≤ A := by
    dsimp [A, T, Y]
    unfold smoothSaddleHTContourHeight
    nlinarith [abs_nonneg t]
  have hAB : A ≤ B := by
    dsimp [A, B, T, Y]
    linarith [smoothSaddleHT_totalHeight_le ht]
  have hAbase : Real.exp (Real.exp 1) ≤ A := hHbase.trans hAheight
  have hBbase : Real.exp (Real.exp 1) ≤ B := by
    dsimp [B, Y]
    have hYpos := smoothSaddleHTFrequencyCeiling_pos y ε
    linarith
  have hAexp : Real.exp 1 ≤ A :=
    (Real.exp_le_exp.mpr
      (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1))).trans hAbase
  have hBexp : Real.exp 1 ≤ B := hAexp.trans hAB
  have hDmono : GafniTao.vinogradovKorobovDenominator A ≤
      GafniTao.vinogradovKorobovDenominator B :=
    GafniTao.monotoneOn_vinogradovKorobovDenominator hAexp hBexp hAB
  have hDA : 0 < GafniTao.vinogradovKorobovDenominator A :=
    GafniTao.vinogradovKorobovDenominator_pos hAbase
  have hcNonneg : 0 ≤ c := by
    by_contra hc'
    have hcneg : c < 0 := lt_of_not_ge hc'
    have hneg : c / GafniTao.vinogradovKorobovDenominator A < 0 :=
      div_neg_of_neg_of_pos hcneg hDA
    linarith [(hZeroFree hAheight).1]
  have hWidthActual : beta + eta ≤
      c / GafniTao.vinogradovKorobovDenominator A := by
    calc
      beta + eta ≤ 3 * eta := by
        dsimp [eta] at hbetaUpper ⊢
        linarith
      _ ≤ 6 * eta := by linarith
      _ ≤ c / GafniTao.vinogradovKorobovDenominator B := by
        simpa [eta, B, Y] using hWidth
      _ ≤ c / GafniTao.vinogradovKorobovDenominator A :=
        div_le_div_of_nonneg_left hcNonneg hDA hDmono
  have hright : -eta ≤ smoothSaddleHTContourRight y beta := by
    have hlog : 0 < Real.log (y : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < y by omega))
    dsimp [eta, smoothSaddleHTContourRight]
    have hinv : 0 < 1 / Real.log (y : ℝ) := one_div_pos.mpr hlog
    linarith
  have hsur : ∀ z ∈ Rectangle
        ((-smoothSaddleHTContourShift y ε : ℂ) -
          (smoothSaddleHTContourHeight y ε : ℂ) * Complex.I)
        (((smoothSaddleHTContourRight y beta : ℝ) : ℂ) +
          (smoothSaddleHTContourHeight y ε : ℂ) * Complex.I),
      GafniTao.sharpZetaSurrogate
        (smoothSaddleHTSourceExponent beta t + z) ≠ 0 := by
    have hthree : 3 * eta ≤ 1 / 2 := by
      dsimp [eta] at hetaSix ⊢
      linarith
    have hraw :=
      smoothSaddleHTSource_shiftedSurrogate_ne_zero_on_rectangle_of_vK_left
        (c := c) (H := H) (left := -eta) (beta := beta) (t := t)
        (T := T) (right := smoothSaddleHTContourRight y beta)
        hZeroFree (by linarith) hright hT.le hAheight
          (by simpa [A, T] using hWidthActual)
    simpa [eta, T] using hraw
  have hlogHigh : 0 ≤ Real.log (3 * Y) := by
    apply Real.log_nonneg
    dsimp [Y]
    linarith [smoothSaddleHTFrequencyCeiling_pos y ε]
  have hHighNonneg : 0 ≤ smoothSaddleHTHighLogDerivativeMajorant y ε := by
    unfold smoothSaddleHTHighLogDerivativeMajorant
    have hAconst := GafniTao.sharpLandauPartialFractionConstant_pos.le
    have hMconst := GafniTao.sharpLandauMassConstant_pos.le
    dsimp [eta, Y] at heta hlogHigh ⊢
    positivity
  have hLeftNonneg : 0 ≤ smoothSaddleHTLeftLogDerivativeMajorant y ε C :=
    hHighNonneg.trans (le_max_right _ _)
  apply norm_smoothSaddleHTSmallBetaContourEdgeContribution_le_analyticMajorant
    hy hbeta ht hHighNonneg hLeftNonneg hsur
  · intro x hx
    have hR := smoothSaddleHT_top_physicalHeight_abs_bounds ht
    have hSigma := smoothSaddleHT_smallBeta_horizontal_physicalReal_bounds
      hetaSix hlogOne hbetaUpper hx
    have hHeight : H ≤ 3 * |t + smoothSaddleHTContourHeight y ε| := by
      linarith [hHY, hR.1]
    exact norm_riemannZeta_logDeriv_threeShift_contourHeight_le_of_vK
      hZeroFree hHbase hy hYbase hWidth (hY8.trans hR.1) hHeight
        hR.2 hSigma.1 hSigma.2
  · intro x hx
    have hR := smoothSaddleHT_bottom_physicalHeight_abs_bounds ht
    have hSigma := smoothSaddleHT_smallBeta_horizontal_physicalReal_bounds
      hetaSix hlogOne hbetaUpper hx
    have hHeight : H ≤ 3 * |t - smoothSaddleHTContourHeight y ε| := by
      linarith [hHY, hR.1]
    exact norm_riemannZeta_logDeriv_threeShift_contourHeight_le_of_vK
      hZeroFree hHbase hy hYbase hWidth (hY8.trans hR.1) hHeight
        hR.2 hSigma.1 hSigma.2
  · intro u hu
    exact norm_riemannZeta_logDeriv_HT_smallBeta_negativeLeft_le_of_vK
      hHbase hEightH hZeroFree hClow hy hYbase hWidth hetaSix hetaFixed
        hbeta hbetaUpper ht hu

end

end Tao2026
