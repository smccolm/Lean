import Tao2026.SmoothNumberSaddleHTMainTermLower

/-!
# Comparing the HT main coefficient with the smooth saddle

This module uses the existing finite Abel estimate for weighted prime powers
to compare the coefficient in the HT Lemma 6 main term with the Rankin ratio.
The comparison is finite and explicit under the canonical cutoff hypothesis
already isolated by the prime-sum development.
-/

open Filter Topology MeasureTheory Set Complex Finset
open scoped ArithmeticFunction.vonMangoldt BigOperators Interval

namespace Tao2026

noncomputable section

/-- An explicit absolute constant in the saddle/main-term comparison. -/
def smoothSaddleHTSaddleComparisonConstant : ℝ :=
  5 * smoothPrimeCountingConstant * (3 + 1 / Real.log 2)

theorem smoothSaddleHTSaddleComparisonConstant_pos :
    0 < smoothSaddleHTSaddleComparisonConstant := by
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos one_lt_two
  have hfactor : 0 < 3 + 1 / Real.log (2 : ℝ) := by positivity
  unfold smoothSaddleHTSaddleComparisonConstant
  exact mul_pos (mul_pos (by norm_num) smoothPrimeCountingConstant_pos) hfactor

/-- A saddle prime term is bounded by a logarithmic endpoint factor times
the corresponding weighted-prime term. -/
theorem smoothSaddlePrimeTerm_le_log_mul_rpow
    {y p : ℕ} (hp : p.Prime) (hpy : p ≤ y)
    {sigma : ℝ} (hsigmaHalf : (1 / 2 : ℝ) ≤ sigma)
    (hsigmaOne : sigma ≤ 1) :
    smoothSaddlePrimeTerm p sigma ≤
      5 * Real.log y * (p : ℝ) ^ (-sigma) := by
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hyPos : (0 : ℝ) < y := by exact_mod_cast hp.pos.trans_le hpy
  have hbase := smoothSaddlePrimeTerm_le_five_mul_rpow_mul_log_div
    (y := p) hp le_rfl hsigmaHalf hsigmaOne
  calc
    smoothSaddlePrimeTerm p sigma ≤
        5 * (p : ℝ) ^ (1 - sigma) * (Real.log p / p) := hbase
    _ = 5 * Real.log p * (p : ℝ) ^ (-sigma) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one]
      calc
        5 * (p : ℝ) ^ (1 - sigma) *
            (Real.log p * (p : ℝ) ^ (-1 : ℝ)) =
            5 * Real.log p *
              ((p : ℝ) ^ (1 - sigma) * (p : ℝ) ^ (-1 : ℝ)) := by ring
        _ = 5 * Real.log p * (p : ℝ) ^ (-sigma) := by
          rw [← Real.rpow_add hpPos]
          congr 2
          ring
    _ ≤ 5 * Real.log y * (p : ℝ) ^ (-sigma) := by
      gcongr

/-- The saddle equation's prime sum is bounded at the same
`y^(1-sigma)/(1-sigma)` scale as the HT main term. -/
theorem smoothSaddlePhiOne_le_ht_mainScale
    {y : ℕ} (hy : 4 ≤ y) {sigma : ℝ}
    (hsigmaHalf : (1 / 2 : ℝ) ≤ sigma) (hsigmaOne : sigma < 1)
    (hlogOne : 1 ≤ Real.log (y : ℝ))
    (hhalf : 2 * smoothSaddleDivisor y sigma ≤ Real.sqrt y) :
    smoothSaddlePhiOne y sigma ≤
      smoothSaddleHTSaddleComparisonConstant *
        ((y : ℝ) ^ (1 - sigma) / (1 - sigma)) := by
  let A : ℝ := (y : ℝ) ^ (1 - sigma)
  let beta : ℝ := 1 - sigma
  let L : ℝ := Real.log y
  let P : ℝ := smoothPrimeCountingConstant
  let Q : ℝ := 1 / Real.log 2 + 2
  have hbeta : 0 < beta := by dsimp [beta]; linarith
  have hbetaOne : beta ≤ 1 := by dsimp [beta]; linarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hL : 0 < L := by dsimp [L]; linarith
  have hP : 0 < P := by exact smoothPrimeCountingConstant_pos
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hsum := primeRpowSum_le_canonicalSaddleScale_two
    hy (show 0 ≤ sigma by linarith) hsigmaOne hlogOne hhalf
  change (∑ p ∈ (Finset.Icc 2 y).filter Nat.Prime,
      (p : ℝ) ^ (-sigma)) ≤ P * A / L +
        P * sigma * (A / beta / L * Q) at hsum
  have hphi : smoothSaddlePhiOne y sigma ≤
      5 * L * ∑ p ∈ (Finset.Icc 2 y).filter Nat.Prime,
        (p : ℝ) ^ (-sigma) := by
    unfold smoothSaddlePhiOne
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    exact smoothSaddlePrimeTerm_le_log_mul_rpow hpData.2
      (Finset.mem_Icc.mp hpData.1).2 hsigmaHalf hsigmaOne.le
  have hphi' : smoothSaddlePhiOne y sigma ≤
      5 * L * (P * A / L + P * sigma * (A / beta / L * Q)) :=
    hphi.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
  have hAdiv : A ≤ A / beta := by
    rw [le_div_iff₀ hbeta]
    nlinarith
  have hsigmaOne' : sigma ≤ 1 := hsigmaOne.le
  calc
    smoothSaddlePhiOne y sigma ≤
        5 * L * (P * A / L + P * sigma * (A / beta / L * Q)) := hphi'
    _ = 5 * P * A + 5 * P * sigma * (A / beta) * Q := by
      field_simp [ne_of_gt hL]
    _ ≤ 5 * P * (A / beta) + 5 * P * (A / beta) * Q := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hAdiv
          (mul_nonneg (by norm_num) hP.le)
      · apply mul_le_mul_of_nonneg_right _ hQ
        have hAbeta : 0 ≤ A / beta := div_nonneg hA hbeta.le
        have hcoeff : 0 ≤ 5 * P * (A / beta) := by positivity
        have hmul := mul_le_mul_of_nonneg_left hsigmaOne' hcoeff
        nlinarith
    _ = smoothSaddleHTSaddleComparisonConstant * (A / beta) := by
      unfold smoothSaddleHTSaddleComparisonConstant
      dsimp [P, Q]
      ring

/-- At the exact smooth saddle, the HT main coefficient controls a fixed
multiple of the Rankin ratio. -/
theorem smoothRankinRatio_div_htConstant_le_saddleMainCoefficient
    {X y : ℕ} (hX : 2 ≤ X) (hy : 4 ≤ y)
    (hsigmaHalf : (1 / 2 : ℝ) ≤ smoothSaddlePoint X y)
    (hsigmaOne : smoothSaddlePoint X y < 1)
    (hlogOne : 1 ≤ Real.log (y : ℝ))
    (hhalf : 2 * smoothSaddleDivisor y (smoothSaddlePoint X y) ≤ Real.sqrt y) :
    smoothRankinRatio X y / smoothSaddleHTSaddleComparisonConstant ≤
      (y : ℝ) ^ (1 - smoothSaddlePoint X y) /
        ((1 - smoothSaddlePoint X y) * Real.log y) := by
  let sigma := smoothSaddlePoint X y
  let A : ℝ := (y : ℝ) ^ (1 - sigma)
  let beta : ℝ := 1 - sigma
  let L : ℝ := Real.log y
  have hbeta : 0 < beta := by dsimp [beta, sigma]; linarith
  have hC : 0 < smoothSaddleHTSaddleComparisonConstant :=
    smoothSaddleHTSaddleComparisonConstant_pos
  have hL : 0 < L := by dsimp [L]; linarith
  have hphi := smoothSaddlePhiOne_le_ht_mainScale
    hy hsigmaHalf hsigmaOne hlogOne hhalf
  rw [smoothSaddlePhiOne_smoothSaddlePoint hX (by omega)] at hphi
  have huL : smoothRankinRatio X y * L ≤
      smoothSaddleHTSaddleComparisonConstant * (A / beta) := by
    calc
      smoothRankinRatio X y * L = Real.log (X : ℝ) := by
        dsimp [L]
        exact smoothRankinRatio_mul_log (by omega)
      _ ≤ smoothSaddleHTSaddleComparisonConstant * (A / beta) := by
        simpa only [sigma, A, beta] using hphi
  apply (div_le_iff₀ hC).2
  change smoothRankinRatio X y ≤
    (A / (beta * L)) * smoothSaddleHTSaddleComparisonConstant
  have heq : A / (beta * L) * smoothSaddleHTSaddleComparisonConstant =
      smoothSaddleHTSaddleComparisonConstant * (A / beta) / L := by
    field_simp [ne_of_gt hbeta, ne_of_gt hL]
  rw [heq]
  exact (le_div_iff₀ hL).2 huL

/-- The HT cosine main term at the exact saddle dominates the source-shaped
Rankin-ratio loss, up to one explicit absolute constant. -/
theorem smoothSaddleHTMangoldtCosineMainTerm_div_log_lower
    {X y : ℕ} (hX : 2 ≤ X) (hy : 4 ≤ y)
    (hsigmaHalf : (1 / 2 : ℝ) ≤ smoothSaddlePoint X y)
    (hsigmaOne : smoothSaddlePoint X y < 1)
    (hlogOne : 1 ≤ Real.log (y : ℝ))
    (hhalf : 2 * smoothSaddleDivisor y (smoothSaddlePoint X y) ≤ Real.sqrt y)
    (t : ℝ) :
    smoothRankinRatio X y /
          (2 * smoothSaddleHTSaddleComparisonConstant) * t ^ 2 /
        ((1 - smoothSaddlePoint X y) ^ 2 + t ^ 2) ≤
      smoothSaddleHTMangoldtCosineMainTerm y
        (1 - smoothSaddlePoint X y) t / Real.log y := by
  let sigma := smoothSaddlePoint X y
  let A : ℝ := (y : ℝ) ^ (1 - sigma)
  let beta : ℝ := 1 - sigma
  let L : ℝ := Real.log y
  let D : ℝ := beta ^ 2 + t ^ 2
  have hbeta : 0 < beta := by dsimp [beta, sigma]; linarith
  have hL : 0 < L := by dsimp [L]; linarith
  have hD : 0 < D := by dsimp [D]; positivity
  have hC : 0 < smoothSaddleHTSaddleComparisonConstant :=
    smoothSaddleHTSaddleComparisonConstant_pos
  have hcomp := smoothRankinRatio_div_htConstant_le_saddleMainCoefficient
    hX hy hsigmaHalf hsigmaOne hlogOne hhalf
  have hmain := smoothSaddleHTMangoldtCosineMainTerm_lower
    (y := y) (t := t) hbeta
  have hfactor : 0 ≤ t ^ 2 / (2 * D) := by positivity
  change smoothRankinRatio X y /
      (2 * smoothSaddleHTSaddleComparisonConstant) * t ^ 2 / D ≤
    smoothSaddleHTMangoldtCosineMainTerm y beta t / L
  calc
    smoothRankinRatio X y /
          (2 * smoothSaddleHTSaddleComparisonConstant) * t ^ 2 / D =
        (smoothRankinRatio X y / smoothSaddleHTSaddleComparisonConstant) *
          (t ^ 2 / (2 * D)) := by
      field_simp [ne_of_gt hC, ne_of_gt hD]
    _ ≤ (A / (beta * L)) * (t ^ 2 / (2 * D)) :=
      mul_le_mul_of_nonneg_right (by
        simpa only [sigma, A, beta, L] using hcomp) hfactor
    _ = (A * t ^ 2 / (2 * beta * D)) / L := by
      field_simp [ne_of_gt hbeta, ne_of_gt hL, ne_of_gt hD]
    _ ≤ smoothSaddleHTMangoldtCosineMainTerm y beta t / L :=
      div_le_div_of_nonneg_right (by
        simpa only [A, D] using hmain) hL.le

end

end Tao2026
