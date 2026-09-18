import Tao2026.SmoothNumberSaddleHTLogDerivativeContour
import Tao2026.SmoothNumberSaddleHTContourEdgeWeighted

/-!
# Analytic bounds for the shifted HT contour edges

The physical logarithmic-derivative estimates are converted here into bounds
for the actual shifted Perron integrand.  On the horizontal edges the Perron
denominator supplies a factor `1 / T`.  On the vertical edge it is retained
pointwise, so the weighted contour lemma pays only logarithmic height.
-/

open Complex Set

namespace Tao2026

noncomputable section

/-- Common pointwise majorant for either horizontal shifted-Perron edge. -/
noncomputable def smoothSaddleHTHorizontalIntegrandMajorant
    (y : ℕ) (beta ε : ℝ) : ℝ :=
  smoothSaddleHTHighLogDerivativeMajorant y ε *
      (y : ℝ) ^ smoothSaddleHTContourRight y beta /
    smoothSaddleHTContourHeight y ε

/-- Numerator retained above the Perron denominator on the left edge. -/
noncomputable def smoothSaddleHTVerticalIntegrandNumerator
    (y : ℕ) (beta ε C : ℝ) : ℝ :=
  smoothSaddleHTLeftLogDerivativeMajorant y ε C *
    (y : ℝ) ^ (beta - smoothSaddleHTContourShift y ε)

private theorem shifted_surrogate_ne_zero_implies_zeta_ne_zero
    {w : ℂ} (hw1 : w ≠ 1)
    (hsur : GafniTao.sharpZetaSurrogate w ≠ 0) :
    riemannZeta w ≠ 0 := by
  intro hzeta
  exact hsur ((GafniTao.sharpZetaSurrogate_eq_zero_iff hw1).2 hzeta)

/-- A physical logarithmic-derivative bound on a horizontal line transfers
to the shifted-Perron integrand, with the imaginary part of the Perron
variable retained in the denominator. -/
theorem norm_smoothSaddleHTShiftedZetaPerronIntegrand_horizontal_le
    {y : ℕ} {beta t x v L : ℝ}
    (hy : 2 ≤ y) (hx : x ≤ smoothSaddleHTContourRight y beta)
    (hv : 0 < |v|) (hphysicalIm : 0 < |t + v|)
    (hsur : GafniTao.sharpZetaSurrogate
      (smoothSaddleHTSourceExponent beta t +
        ((x : ℂ) + (v : ℂ) * Complex.I)) ≠ 0)
    (hlog : ‖deriv riemannZeta
          (((1 - beta + x : ℝ) : ℂ) +
            ((t + v : ℝ) : ℂ) * Complex.I) /
        riemannZeta
          (((1 - beta + x : ℝ) : ℂ) +
            ((t + v : ℝ) : ℂ) * Complex.I)‖ ≤ L)
    (hL : 0 ≤ L) :
    ‖smoothSaddleHTShiftedZetaPerronIntegrand (y : ℝ)
        (smoothSaddleHTSourceExponent beta t)
        ((x : ℂ) + (v : ℂ) * Complex.I)‖ ≤
      L * (y : ℝ) ^ smoothSaddleHTContourRight y beta / |v| := by
  let z : ℂ := (x : ℂ) + (v : ℂ) * Complex.I
  let w : ℂ := smoothSaddleHTSourceExponent beta t + z
  have hyReal : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast (show 1 ≤ y by omega)
  have hz0 : z ≠ 0 := by
    intro hz
    have him := congrArg Complex.im hz
    have hv0 : v = 0 := by simpa [z] using him
    exact (ne_of_gt hv) (abs_eq_zero.mpr hv0)
  have hw1 : w ≠ 1 := by
    intro hw
    have him := congrArg Complex.im hw
    have htv0 : t + v = 0 := by
      simpa [w, z, smoothSaddleHTSourceExponent] using him
    exact (ne_of_gt hphysicalIm) (abs_eq_zero.mpr htv0)
  have hzeta : riemannZeta w ≠ 0 :=
    shifted_surrogate_ne_zero_implies_zeta_ne_zero hw1 (by simpa [w, z] using hsur)
  have hw : w =
      ((1 - beta + x : ℝ) : ℂ) + ((t + v : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [w, z, smoothSaddleHTSourceExponent]
  have hraw := norm_smoothSaddleHTShiftedZetaPerronIntegrand_le
    (y := (y : ℝ)) (s := smoothSaddleHTSourceExponent beta t) (z := z)
    (by positivity) hz0 (by simpa [w] using hw1) (by simpa [w] using hzeta)
    (by simpa [w, hw] using hlog)
  have hrpow : (y : ℝ) ^ x ≤
      (y : ℝ) ^ smoothSaddleHTContourRight y beta :=
    Real.rpow_le_rpow_of_exponent_le hyReal hx
  have hvnorm : |v| ≤ ‖z‖ := by
    have h := Complex.abs_im_le_norm z
    simpa [z] using h
  have hnum : 0 ≤ L * (y : ℝ) ^ smoothSaddleHTContourRight y beta :=
    mul_nonneg hL (Real.rpow_nonneg (by positivity) _)
  calc
    ‖smoothSaddleHTShiftedZetaPerronIntegrand (y : ℝ)
        (smoothSaddleHTSourceExponent beta t) z‖ ≤
        L * (y : ℝ) ^ z.re / ‖z‖ := hraw
    _ = L * (y : ℝ) ^ x / ‖z‖ := by simp [z]
    _ ≤ L * (y : ℝ) ^ smoothSaddleHTContourRight y beta / ‖z‖ := by
      gcongr
    _ ≤ L * (y : ℝ) ^ smoothSaddleHTContourRight y beta / |v| :=
      div_le_div_of_nonneg_left hnum hv hvnorm

/-- A physical logarithmic-derivative bound on the shifted left line
transfers without discarding the Perron denominator. -/
theorem norm_smoothSaddleHTShiftedZetaPerronIntegrand_left_le
    {y : ℕ} {beta ε t u L : ℝ}
    (hy : 2 ≤ y) (hbetaShift : smoothSaddleHTContourShift y ε < beta)
    (hsur : GafniTao.sharpZetaSurrogate
      (smoothSaddleHTSourceExponent beta t +
        (((beta - smoothSaddleHTContourShift y ε : ℝ) : ℂ) +
          (u : ℂ) * Complex.I)) ≠ 0)
    (hlog : ‖deriv riemannZeta
          (((1 - smoothSaddleHTContourShift y ε : ℝ) : ℂ) +
            ((t + u : ℝ) : ℂ) * Complex.I) /
        riemannZeta
          (((1 - smoothSaddleHTContourShift y ε : ℝ) : ℂ) +
            ((t + u : ℝ) : ℂ) * Complex.I)‖ ≤ L) :
    ‖smoothSaddleHTShiftedZetaPerronIntegrand (y : ℝ)
        (smoothSaddleHTSourceExponent beta t)
        (((beta - smoothSaddleHTContourShift y ε : ℝ) : ℂ) +
          (u : ℂ) * Complex.I)‖ ≤
      L * (y : ℝ) ^ (beta - smoothSaddleHTContourShift y ε) /
        ‖((beta - smoothSaddleHTContourShift y ε : ℝ) : ℂ) +
          (u : ℂ) * Complex.I‖ := by
  let left : ℝ := beta - smoothSaddleHTContourShift y ε
  let z : ℂ := (left : ℂ) + (u : ℂ) * Complex.I
  let w : ℂ := smoothSaddleHTSourceExponent beta t + z
  have hleft : 0 < left := by dsimp [left]; linarith
  have hz0 : z ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    have : left = 0 := by simpa [z] using hre
    linarith
  have heta := smoothSaddleHTContourShift_pos hy ε
  have hw1 : w ≠ 1 := by
    intro hw
    have hre := congrArg Complex.re hw
    have : 1 - smoothSaddleHTContourShift y ε = 1 := by
      simpa [w, z, left, smoothSaddleHTSourceExponent] using hre
    linarith
  have hzeta : riemannZeta w ≠ 0 :=
    shifted_surrogate_ne_zero_implies_zeta_ne_zero hw1 (by simpa [w, z, left] using hsur)
  have hw : w =
      ((1 - smoothSaddleHTContourShift y ε : ℝ) : ℂ) +
        ((t + u : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;>
      simp [w, z, left, smoothSaddleHTSourceExponent]
  have hraw := norm_smoothSaddleHTShiftedZetaPerronIntegrand_le
    (y := (y : ℝ)) (s := smoothSaddleHTSourceExponent beta t) (z := z)
    (by positivity) hz0 (by simpa [w] using hw1) (by simpa [w] using hzeta)
    (by simpa [w, hw] using hlog)
  simpa [z, left] using hraw

/-- The three physical logarithmic-derivative bounds, together with one
surrogate-zero-free rectangle, discharge the complete weighted contour-edge
estimate. -/
theorem norm_smoothSaddleHTContourEdgeContribution_le_analyticMajorant
    {y : ℕ} {beta ε t C : ℝ}
    (hy : 2 ≤ y)
    (hbetaShift : smoothSaddleHTContourShift y ε < beta)
    (ht : |t| ≤ smoothSaddleHTFrequencyCeiling y ε)
    (hHighNonneg : 0 ≤ smoothSaddleHTHighLogDerivativeMajorant y ε)
    (hLeftNonneg : 0 ≤ smoothSaddleHTLeftLogDerivativeMajorant y ε C)
    (hsur : ∀ z ∈ Rectangle
        (((beta - smoothSaddleHTContourShift y ε : ℝ) : ℂ) -
          (smoothSaddleHTContourHeight y ε : ℂ) * Complex.I)
        (((smoothSaddleHTContourRight y beta : ℝ) : ℂ) +
          (smoothSaddleHTContourHeight y ε : ℂ) * Complex.I),
      GafniTao.sharpZetaSurrogate
        (smoothSaddleHTSourceExponent beta t + z) ≠ 0)
    (htopLog : ∀ x ∈ Set.Icc
        (beta - smoothSaddleHTContourShift y ε)
        (smoothSaddleHTContourRight y beta),
      ‖deriv riemannZeta
            (((1 - beta + x : ℝ) : ℂ) +
              ((t + smoothSaddleHTContourHeight y ε : ℝ) : ℂ) * Complex.I) /
          riemannZeta
            (((1 - beta + x : ℝ) : ℂ) +
              ((t + smoothSaddleHTContourHeight y ε : ℝ) : ℂ) * Complex.I)‖ ≤
        smoothSaddleHTHighLogDerivativeMajorant y ε)
    (hbottomLog : ∀ x ∈ Set.Icc
        (beta - smoothSaddleHTContourShift y ε)
        (smoothSaddleHTContourRight y beta),
      ‖deriv riemannZeta
            (((1 - beta + x : ℝ) : ℂ) +
              ((t - smoothSaddleHTContourHeight y ε : ℝ) : ℂ) * Complex.I) /
          riemannZeta
            (((1 - beta + x : ℝ) : ℂ) +
              ((t - smoothSaddleHTContourHeight y ε : ℝ) : ℂ) * Complex.I)‖ ≤
        smoothSaddleHTHighLogDerivativeMajorant y ε)
    (hleftLog : ∀ u ∈ Set.Icc
        (-smoothSaddleHTContourHeight y ε)
        (smoothSaddleHTContourHeight y ε),
      ‖deriv riemannZeta
            (((1 - smoothSaddleHTContourShift y ε : ℝ) : ℂ) +
              ((t + u : ℝ) : ℂ) * Complex.I) /
          riemannZeta
            (((1 - smoothSaddleHTContourShift y ε : ℝ) : ℂ) +
              ((t + u : ℝ) : ℂ) * Complex.I)‖ ≤
        smoothSaddleHTLeftLogDerivativeMajorant y ε C) :
    ‖smoothSaddleHTContourEdgeContribution y beta ε t‖ ≤
      smoothSaddleHTContourEdgeWeightedMajorant y beta ε
        (smoothSaddleHTHorizontalIntegrandMajorant y beta ε)
        (smoothSaddleHTVerticalIntegrandNumerator y beta ε C) := by
  let eta := smoothSaddleHTContourShift y ε
  let T := smoothSaddleHTContourHeight y ε
  let right := smoothSaddleHTContourRight y beta
  have heta := smoothSaddleHTContourShift_pos hy ε
  have hT := smoothSaddleHTContourHeight_pos y ε
  have hright := smoothSaddleHTContourRight_gt hy beta
  have hlr : beta - eta ≤ right := by
    dsimp [eta, right]
    linarith
  have hTorder : -T ≤ T := by linarith
  have htopPhysical := smoothSaddleHT_top_physicalHeight_abs_bounds ht
  have hbottomPhysical := smoothSaddleHT_bottom_physicalHeight_abs_bounds ht
  have hYpos := smoothSaddleHTFrequencyCeiling_pos y ε
  apply norm_smoothSaddleHTContourEdgeContribution_le_weightedMajorant
    hy hbetaShift
  · unfold smoothSaddleHTVerticalIntegrandNumerator
    exact mul_nonneg hLeftNonneg (Real.rpow_nonneg (by positivity) _)
  · intro x hx
    have hsurPoint : GafniTao.sharpZetaSurrogate
        (smoothSaddleHTSourceExponent beta t +
          ((x : ℂ) - (T : ℂ) * Complex.I)) ≠ 0 := by
      apply hsur
      change
        ((x : ℂ) - (T : ℂ) * Complex.I).re ∈
            Set.uIcc
              (((beta - smoothSaddleHTContourShift y ε : ℝ) : ℂ) -
                (smoothSaddleHTContourHeight y ε : ℂ) * Complex.I).re
              (((smoothSaddleHTContourRight y beta : ℝ) : ℂ) +
                (smoothSaddleHTContourHeight y ε : ℂ) * Complex.I).re ∧
          ((x : ℂ) - (T : ℂ) * Complex.I).im ∈
            Set.uIcc
              (((beta - smoothSaddleHTContourShift y ε : ℝ) : ℂ) -
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
        ((x : ℂ) + (T : ℂ) * Complex.I).re ∈
            Set.uIcc
              (((beta - smoothSaddleHTContourShift y ε : ℝ) : ℂ) -
                (smoothSaddleHTContourHeight y ε : ℂ) * Complex.I).re
              (((smoothSaddleHTContourRight y beta : ℝ) : ℂ) +
                (smoothSaddleHTContourHeight y ε : ℂ) * Complex.I).re ∧
          ((x : ℂ) + (T : ℂ) * Complex.I).im ∈
            Set.uIcc
              (((beta - smoothSaddleHTContourShift y ε : ℝ) : ℂ) -
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
      hy hx.2 (v := T)
      (abs_pos.mpr (ne_of_gt hT))
      (by simpa [T] using
        (show 0 < |t + smoothSaddleHTContourHeight y ε| from
          hYpos.trans_le htopPhysical.1))
      (by simpa [T] using hsurPoint)
      (by simpa [T] using htopLog x hx)
      hHighNonneg
    simpa [smoothSaddleHTHorizontalIntegrandMajorant, T, abs_of_pos hT]
      using hpoint
  · intro u hu
    have hsurPoint : GafniTao.sharpZetaSurrogate
        (smoothSaddleHTSourceExponent beta t +
          (((beta - eta : ℝ) : ℂ) + (u : ℂ) * Complex.I)) ≠ 0 := by
      apply hsur
      change
        (((beta - eta : ℝ) : ℂ) + (u : ℂ) * Complex.I).re ∈
            Set.uIcc
              (((beta - smoothSaddleHTContourShift y ε : ℝ) : ℂ) -
                (smoothSaddleHTContourHeight y ε : ℂ) * Complex.I).re
              (((smoothSaddleHTContourRight y beta : ℝ) : ℂ) +
                (smoothSaddleHTContourHeight y ε : ℂ) * Complex.I).re ∧
          (((beta - eta : ℝ) : ℂ) + (u : ℂ) * Complex.I).im ∈
            Set.uIcc
              (((beta - smoothSaddleHTContourShift y ε : ℝ) : ℂ) -
                (smoothSaddleHTContourHeight y ε : ℂ) * Complex.I).im
              (((smoothSaddleHTContourRight y beta : ℝ) : ℂ) +
                (smoothSaddleHTContourHeight y ε : ℂ) * Complex.I).im
      constructor
      · have : beta - eta ∈ Set.uIcc (beta - eta) right := by
          rw [Set.uIcc_of_le hlr]
          exact ⟨le_rfl, hlr⟩
        convert this using 1 <;> simp [eta, right]
      · simpa [Set.uIcc_of_le hTorder, T] using hu
    have hpoint := norm_smoothSaddleHTShiftedZetaPerronIntegrand_left_le
      hy hbetaShift (by simpa [eta] using hsurPoint) (hleftLog u hu)
    simpa [smoothSaddleHTVerticalIntegrandNumerator, eta] using hpoint

/-- The VK/Landau contour bounds specialize all hypotheses of the analytic
edge theorem.  The nine-frequency spare width also implies the literal
zero-free condition at the actual translated rectangle height. -/
theorem norm_smoothSaddleHTContourEdgeContribution_le_analyticMajorant_of_vK
    {c H beta ε t C : ℝ} {y : ℕ}
    (hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H)
    (hHbase : Real.exp (Real.exp 1) ≤ H) (hEightH : 8 ≤ H)
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
    (hY8 : 8 ≤ smoothSaddleHTFrequencyCeiling y ε)
    (hHY : H ≤ smoothSaddleHTFrequencyCeiling y ε)
    (hWidth : 2 * smoothSaddleHTContourShift y ε ≤ c /
      GafniTao.vinogradovKorobovDenominator
        (9 * smoothSaddleHTFrequencyCeiling y ε))
    (hetaHalf : smoothSaddleHTContourShift y ε ≤ 1 / 2)
    (hetaFixed : smoothSaddleHTContourShift y ε ≤
      c / (2 * GafniTao.vinogradovKorobovDenominator H))
    (hbetaShift : smoothSaddleHTContourShift y ε < beta)
    (hlogOne : 1 ≤ Real.log y)
    (ht : |t| ≤ smoothSaddleHTFrequencyCeiling y ε) :
    ‖smoothSaddleHTContourEdgeContribution y beta ε t‖ ≤
      smoothSaddleHTContourEdgeWeightedMajorant y beta ε
        (smoothSaddleHTHorizontalIntegrandMajorant y beta ε)
        (smoothSaddleHTVerticalIntegrandNumerator y beta ε C) := by
  let eta := smoothSaddleHTContourShift y ε
  let Y := smoothSaddleHTFrequencyCeiling y ε
  let T := smoothSaddleHTContourHeight y ε
  let A := |t| + T
  let B := 9 * Y
  have heta : 0 < eta := by
    dsimp [eta]
    exact smoothSaddleHTContourShift_pos hy ε
  have hT : 0 < T := by
    dsimp [T]
    exact smoothSaddleHTContourHeight_pos y ε
  have hAheight : H ≤ A := by
    dsimp [A, T, Y]
    unfold smoothSaddleHTContourHeight
    have habs := abs_nonneg t
    linarith
  have hAB : A ≤ B := by
    dsimp [A, B, T, Y]
    have htotal := smoothSaddleHT_totalHeight_le ht
    linarith
  have hAbase : Real.exp (Real.exp 1) ≤ A := hHbase.trans hAheight
  have hBbase : Real.exp (Real.exp 1) ≤ B := by
    dsimp [B, Y]
    have hYpos := smoothSaddleHTFrequencyCeiling_pos y ε
    linarith
  have hAexp : Real.exp 1 ≤ A :=
    (Real.exp_le_exp.mpr (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1))).trans hAbase
  have hBexp : Real.exp 1 ≤ B := hAexp.trans hAB
  have hDmono : GafniTao.vinogradovKorobovDenominator A ≤
      GafniTao.vinogradovKorobovDenominator B :=
    GafniTao.monotoneOn_vinogradovKorobovDenominator hAexp hBexp hAB
  have hDA : 0 < GafniTao.vinogradovKorobovDenominator A :=
    GafniTao.vinogradovKorobovDenominator_pos hAbase
  have hcNonneg : 0 ≤ c := by
    by_contra hc
    have hcneg : c < 0 := lt_of_not_ge hc
    have := (hZeroFree hAheight).1
    have : c / GafniTao.vinogradovKorobovDenominator A < 0 :=
      div_neg_of_neg_of_pos hcneg hDA
    linarith
  have hWidthActual : eta ≤
      c / GafniTao.vinogradovKorobovDenominator A := by
    calc
      eta ≤ 2 * eta := by linarith
      _ ≤ c / GafniTao.vinogradovKorobovDenominator B := by
        simpa [eta, B, Y] using hWidth
      _ ≤ c / GafniTao.vinogradovKorobovDenominator A :=
        div_le_div_of_nonneg_left hcNonneg hDA hDmono
  have hright := smoothSaddleHTContourRight_gt hy beta
  have hsur : ∀ z ∈ Rectangle
        (((beta - smoothSaddleHTContourShift y ε : ℝ) : ℂ) -
          (smoothSaddleHTContourHeight y ε : ℂ) * Complex.I)
        (((smoothSaddleHTContourRight y beta : ℝ) : ℂ) +
          (smoothSaddleHTContourHeight y ε : ℂ) * Complex.I),
      GafniTao.sharpZetaSurrogate
        (smoothSaddleHTSourceExponent beta t + z) ≠ 0 := by
    apply smoothSaddleHTSource_shiftedSurrogate_ne_zero_on_rectangle_of_vK
      hZeroFree
    · exact hetaHalf.trans (by norm_num)
    · linarith
    · exact hT.le
    · exact hAheight
    · simpa [eta, A, T] using hWidthActual
  have hlogHigh : 0 ≤ Real.log (3 * Y) := by
    apply Real.log_nonneg
    dsimp [Y]
    linarith
  have hHighNonneg : 0 ≤ smoothSaddleHTHighLogDerivativeMajorant y ε := by
    unfold smoothSaddleHTHighLogDerivativeMajorant
    have hAconst := GafniTao.sharpLandauPartialFractionConstant_pos.le
    have hMconst := GafniTao.sharpLandauMassConstant_pos.le
    dsimp [eta, Y] at heta hlogHigh ⊢
    positivity
  have hLeftNonneg : 0 ≤ smoothSaddleHTLeftLogDerivativeMajorant y ε C :=
    hHighNonneg.trans (le_max_right _ _)
  apply norm_smoothSaddleHTContourEdgeContribution_le_analyticMajorant
    hy hbetaShift ht hHighNonneg hLeftNonneg hsur
  · intro x hx
    exact norm_riemannZeta_logDeriv_HT_top_le_of_vK
      hZeroFree hHbase hy hYbase hY8 hHY hWidth hetaHalf hlogOne ht hx
  · intro x hx
    exact norm_riemannZeta_logDeriv_HT_bottom_le_of_vK
      hZeroFree hHbase hy hYbase hY8 hHY hWidth hetaHalf hlogOne ht hx
  · intro u hu
    exact norm_riemannZeta_logDeriv_HT_left_le_of_vK
      hHbase hEightH hZeroFree hClow hy hYbase hWidth hetaHalf hetaFixed ht hu

end

end Tao2026
