import Tao2026.SmoothNumberSaddleHTPrimePowerBound

/-!
# Lower bound for the Hildebrand--Tenenbaum cosine main term

The Cartesian main term from HT Lemma 6 is bounded below uniformly in its
phase by a rational quadratic loss.  Combining this bound with the explicit
higher-prime-power estimate gives the complete algebraic lower bound for the
Euler-product cosine loss.  What remains is comparison with the saddle
parameter and the analytic proof of the Lemma 6 transform proposition.
-/

open Filter Topology MeasureTheory Set Complex Finset
open scoped ArithmeticFunction.vonMangoldt BigOperators Interval

namespace Tao2026

noncomputable section

/-- The elementary main term in the cosine corollary to HT Lemma 6 has the
uniform quadratic lower bound needed for Lemma 8(ii). -/
theorem smoothSaddleHTMangoldtCosineMainTerm_lower
    {y : ℕ} {β t : ℝ} (hβ : 0 < β) :
    (y : ℝ) ^ β * t ^ 2 / (2 * β * (β ^ 2 + t ^ 2)) ≤
      smoothSaddleHTMangoldtCosineMainTerm y β t := by
  let D : ℝ := β ^ 2 + t ^ 2
  let r : ℝ := Real.sqrt D
  let θ : ℝ := t * Real.log y
  have hD : 0 < D := by dsimp [D]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hrSq : r ^ 2 = D := by
    dsimp [r]
    exact Real.sq_sqrt hD.le
  have hlinear : β * Real.cos θ + t * Real.sin θ ≤ r := by
    apply Real.le_sqrt_of_sq_le
    dsimp [r, D]
    nlinarith [sq_nonneg (β * Real.sin θ - t * Real.cos θ),
      Real.sin_sq_add_cos_sq θ]
  have hcore : t ^ 2 / (2 * β * D) ≤ 1 / β - r / D := by
    rw [div_le_iff₀ (mul_pos (mul_pos (by norm_num) hβ) hD)]
    field_simp [ne_of_gt hβ, ne_of_gt hD]
    have hβr : β ≤ r := by
      apply Real.le_sqrt_of_sq_le
      dsimp [r, D]
      nlinarith
    nlinarith
  rw [smoothSaddleHTMangoldtCosineMainTerm_eq
    (by positivity : β ^ 2 + t ^ 2 ≠ 0)]
  change (y : ℝ) ^ β * t ^ 2 / (2 * β * D) ≤
    (y : ℝ) ^ β / β -
      (y : ℝ) ^ β * (β * Real.cos θ + t * Real.sin θ) / D
  have hyPow : 0 ≤ (y : ℝ) ^ β := Real.rpow_nonneg (by positivity) _
  calc
    (y : ℝ) ^ β * t ^ 2 / (2 * β * D) =
        (y : ℝ) ^ β * (t ^ 2 / (2 * β * D)) := by ring
    _ ≤ (y : ℝ) ^ β * (1 / β - r / D) :=
      mul_le_mul_of_nonneg_left hcore hyPow
    _ ≤ (y : ℝ) ^ β / β -
        (y : ℝ) ^ β * (β * Real.cos θ + t * Real.sin θ) / D := by
      have hmul := mul_le_mul_of_nonneg_left hlinear hyPow
      have hscaled := div_le_div_of_nonneg_right hmul hD.le
      calc
        (y : ℝ) ^ β * (1 / β - r / D) =
            (y : ℝ) ^ β / β - (y : ℝ) ^ β * r / D := by ring
        _ ≤ (y : ℝ) ^ β / β -
            (y : ℝ) ^ β * (β * Real.cos θ + t * Real.sin θ) / D :=
          sub_le_sub_left hscaled _

/-- HT Lemma 6 with a displayed constant, the main-term lower bound, and HT
Lemma 5 combine into one fully explicit lower bound for the Euler-product
loss. -/
theorem SmoothSaddleHTMangoldtTransformEstimateAt.cosineLoss_lower_bound_explicit
    {ε C : ℝ} (hHT : SmoothSaddleHTMangoldtTransformEstimateAt ε C)
    {y : ℕ} {sigma t : ℝ}
    (hy : 2 ≤ y) (hsigmaHalf : (1 / 2 : ℝ) ≤ sigma)
    (hsigmaOne : sigma < 1)
    (ht : |t| ≤ smoothSaddleHTFrequencyCeiling y ε) :
    ((y : ℝ) ^ (1 - sigma) * t ^ 2 /
          (2 * (1 - sigma) * ((1 - sigma) ^ 2 + t ^ 2)) -
        2 * C * smoothSaddleHTMangoldtError y (1 - sigma) ε -
        2 * ((2 * (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹) *
          (Real.log 4 * (2 + Real.log y)))) / Real.log y ≤
      smoothSaddleCosineLoss y sigma t := by
  have hsigmaPos : 0 < sigma := lt_of_lt_of_le (by norm_num) hsigmaHalf
  have hbeta : 0 < 1 - sigma := sub_pos.mpr hsigmaOne
  have hlog : 0 < Real.log y := Real.log_pos (by exact_mod_cast hy)
  have hmain := smoothSaddleHTMangoldtCosineMainTerm_lower
    (y := y) (t := t) hbeta
  have hrem := smoothSaddleHTPrimePowerRemainder_le_log hy hsigmaHalf
  have hbridge := hHT.cosineLoss_lower_bound hy hsigmaPos hsigmaOne ht
  calc
    ((y : ℝ) ^ (1 - sigma) * t ^ 2 /
          (2 * (1 - sigma) * ((1 - sigma) ^ 2 + t ^ 2)) -
        2 * C * smoothSaddleHTMangoldtError y (1 - sigma) ε -
        2 * ((2 * (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹) *
          (Real.log 4 * (2 + Real.log y)))) / Real.log y ≤
        (smoothSaddleHTMangoldtCosineMainTerm y (1 - sigma) t -
          2 * C * smoothSaddleHTMangoldtError y (1 - sigma) ε -
          2 * smoothSaddleHTPrimePowerRemainder y sigma) / Real.log y := by
      apply div_le_div_of_nonneg_right _ hlog.le
      linarith
    _ ≤ smoothSaddleCosineLoss y sigma t := hbridge

end

end Tao2026
