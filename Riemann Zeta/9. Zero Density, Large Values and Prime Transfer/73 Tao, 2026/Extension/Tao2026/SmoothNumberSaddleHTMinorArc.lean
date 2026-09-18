import Tao2026.SmoothNumberSaddleHTFinitePrefix
import Tao2026.SmoothNumberSaddleHTSaddleComparisonSharp

/-!
# From HT Lemma 6 to the Hildebrand--Tenenbaum minor arc

The all-`y` Mangoldt-transform estimate supplies the cosine-loss lower bound
used in HT Lemma 8(ii).  This file isolates the remaining scalar absorption:
once the Lemma-6 error and the prime-power remainder use at most half of the
available main loss, the normalized saddle characteristic satisfies the
source minor-arc contract with an explicit absolute coefficient.
-/

open Filter Topology Set Complex Finset
open scoped ArithmeticFunction.vonMangoldt BigOperators Interval

namespace Tao2026

noncomputable section

/-- Explicit coefficient obtained by combining the factor-four main/error
split with the global Euler-product factor `1/96`. -/
noncomputable def smoothSaddleHTMinorArcCoefficient : ℝ :=
  1 / (384 * smoothSaddleHTSharpComparisonConstant)

theorem smoothSaddleHTMinorArcCoefficient_pos :
    0 < smoothSaddleHTMinorArcCoefficient := by
  unfold smoothSaddleHTMinorArcCoefficient
  exact one_div_pos.mpr
    (mul_pos (by norm_num) smoothSaddleHTSharpComparisonConstant_pos)

/-- If the two lower-order terms use at most one quarter of the rational HT
loss, Lemma 6 and the sharp saddle comparison leave another quarter as a
uniform lower bound for the Euler-product cosine loss. -/
theorem SmoothSaddleHTMangoldtTransformEstimateAt.htLoss_div_four_le_cosineLoss
    {epsilon C : ℝ} (hHT : SmoothSaddleHTMangoldtTransformEstimateAt epsilon C)
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    (hsigmaHalf : (1 / 2 : ℝ) ≤ smoothSaddlePoint X y)
    (hsigmaOne : smoothSaddlePoint X y < 1) {t : ℝ}
    (ht : |t| ≤ smoothSaddleHTFrequencyCeiling y epsilon)
    (herror :
      (2 * C * smoothSaddleHTMangoldtError y
          (1 - smoothSaddlePoint X y) epsilon +
        2 * smoothSaddleHTPrimePowerRemainder y (smoothSaddlePoint X y)) /
          Real.log y ≤
        smoothSaddleHildebrandTenenbaumLoss X y t /
          (4 * smoothSaddleHTSharpComparisonConstant)) :
    smoothSaddleHildebrandTenenbaumLoss X y t /
        (4 * smoothSaddleHTSharpComparisonConstant) ≤
      smoothSaddleCosineLoss y (smoothSaddlePoint X y) t := by
  let sigma := smoothSaddlePoint X y
  let E := 2 * C * smoothSaddleHTMangoldtError y (1 - sigma) epsilon +
    2 * smoothSaddleHTPrimePowerRemainder y sigma
  let L := smoothSaddleHildebrandTenenbaumLoss X y t
  let K := smoothSaddleHTSharpComparisonConstant
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hmain := smoothSaddleHTMangoldtCosineMainTerm_div_log_lower_sharp
    hX hy hsigmaHalf hsigmaOne t
  have hbridge := hHT.cosineLoss_lower_bound hy
    (lt_of_lt_of_le (by norm_num) hsigmaHalf) hsigmaOne ht
  have hmain' : L / (2 * K) ≤
      smoothSaddleHTMangoldtCosineMainTerm y (1 - sigma) t /
        Real.log y := by
    have hrewrite : L / (2 * K) =
        smoothRankinRatio X y /
            (2 * smoothSaddleHTSharpComparisonConstant) * t ^ 2 /
          ((1 - smoothSaddlePoint X y) ^ 2 + t ^ 2) := by
      dsimp [L, K]
      unfold smoothSaddleHildebrandTenenbaumLoss
      ring
    rw [hrewrite]
    simpa only [sigma] using hmain
  have hbridge' :
      (smoothSaddleHTMangoldtCosineMainTerm y (1 - sigma) t - E) /
          Real.log y ≤ smoothSaddleCosineLoss y sigma t := by
    simpa only [sigma, E, sub_sub] using hbridge
  have herror' : E / Real.log y ≤ L / (4 * K) := by
    simpa only [sigma, E, L, K] using herror
  have hsplit :
      (smoothSaddleHTMangoldtCosineMainTerm y (1 - sigma) t - E) /
          Real.log y =
        smoothSaddleHTMangoldtCosineMainTerm y (1 - sigma) t /
            Real.log y - E / Real.log y := by ring
  rw [hsplit] at hbridge'
  have hK : 0 < K := by
    dsimp [K]
    exact smoothSaddleHTSharpComparisonConstant_pos
  have : L / (4 * K) ≤
      smoothSaddleHTMangoldtCosineMainTerm y (1 - sigma) t /
          Real.log y - E / Real.log y := by
    have hhalf : L / (2 * K) - L / (4 * K) = L / (4 * K) := by
      field_simp [ne_of_gt hK]
      ring
    rw [← hhalf]
    exact sub_le_sub hmain' herror'
  exact this.trans hbridge'

/-- A cosine-loss lower bound immediately gives the source-facing HT
minor-arc characteristic estimate. -/
theorem smoothSaddleHildebrandTenenbaumMinorArcBoundAt_of_cosineLoss
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    (hsigmaHalf : (1 / 2 : ℝ) ≤ smoothSaddlePoint X y)
    {lower upper : ℝ}
    (hloss : ∀ t : ℝ, lower ≤ |t| → |t| ≤ upper →
      smoothSaddleHildebrandTenenbaumLoss X y t /
          (4 * smoothSaddleHTSharpComparisonConstant) ≤
        smoothSaddleCosineLoss y (smoothSaddlePoint X y) t) :
    SmoothSaddleHildebrandTenenbaumMinorArcBoundAt X y
      smoothSaddleHTMinorArcCoefficient lower upper := by
  intro t htLower htUpper
  have hsd := smoothSaddleStandardDeviation_pos hX hy
  rw [smoothSaddleNormalizedCharacteristic, norm_mul,
    Complex.norm_exp_ofReal_mul_I, one_mul]
  have harg : -t * smoothSaddleStandardDeviation X y /
      smoothSaddleStandardDeviation X y = -t := by
    field_simp [hsd.ne']
  rw [harg]
  have hcharacteristic := norm_smoothTiltedCharacteristic_le_cosineLoss
    y hsigmaHalf (-t)
  rw [smoothSaddleCosineLoss_neg] at hcharacteristic
  calc
    ‖smoothTiltedCharacteristic y (smoothSaddlePoint X y) (-t)‖ ≤
        Real.exp (-(smoothSaddleCosineLoss y
          (smoothSaddlePoint X y) t / 96)) := hcharacteristic
    _ ≤ Real.exp (-(smoothSaddleHTMinorArcCoefficient *
        smoothSaddleHildebrandTenenbaumLoss X y t)) := by
      apply Real.exp_le_exp.mpr
      have h := hloss t htLower htUpper
      unfold smoothSaddleHTMinorArcCoefficient
      have hK := smoothSaddleHTSharpComparisonConstant_pos
      apply neg_le_neg
      calc
        1 / (384 * smoothSaddleHTSharpComparisonConstant) *
              smoothSaddleHildebrandTenenbaumLoss X y t =
            (smoothSaddleHildebrandTenenbaumLoss X y t /
              (4 * smoothSaddleHTSharpComparisonConstant)) / 96 := by
          field_simp [ne_of_gt hK]
          ring
        _ ≤ smoothSaddleCosineLoss y (smoothSaddlePoint X y) t / 96 :=
          div_le_div_of_nonneg_right h (by norm_num)

/-- Fixed-parameter assembly of HT Lemma 8(ii): the proved Lemma-6 estimate
and a uniform scalar error absorption imply the exact minor-arc contract. -/
theorem SmoothSaddleHTMangoldtTransformEstimateAt.minorArcBoundAt
    {epsilon C : ℝ} (hHT : SmoothSaddleHTMangoldtTransformEstimateAt epsilon C)
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    (hsigmaHalf : (1 / 2 : ℝ) ≤ smoothSaddlePoint X y)
    (hsigmaOne : smoothSaddlePoint X y < 1)
    {lower upper : ℝ}
    (hupper : upper ≤ smoothSaddleHTFrequencyCeiling y epsilon)
    (herror : ∀ t : ℝ, lower ≤ |t| → |t| ≤ upper →
      (2 * C * smoothSaddleHTMangoldtError y
          (1 - smoothSaddlePoint X y) epsilon +
        2 * smoothSaddleHTPrimePowerRemainder y (smoothSaddlePoint X y)) /
          Real.log y ≤
        smoothSaddleHildebrandTenenbaumLoss X y t /
          (4 * smoothSaddleHTSharpComparisonConstant)) :
    SmoothSaddleHildebrandTenenbaumMinorArcBoundAt X y
      smoothSaddleHTMinorArcCoefficient lower upper := by
  apply smoothSaddleHildebrandTenenbaumMinorArcBoundAt_of_cosineLoss
    hX hy hsigmaHalf
  intro t htLower htUpper
  exact hHT.htLoss_div_four_le_cosineLoss hX hy hsigmaHalf hsigmaOne
    (htUpper.trans hupper) (herror t htLower htUpper)

end

end Tao2026
