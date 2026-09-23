import TaoTrudgianYang2025.BetaReflection
import TaoTrudgianYang2025.BetaClosedDuality

/-!
# Closed half-interval criterion for actual analytic exponent pairs

For a candidate whose affine slope is at least one half, the proved beta
reflection supplies the other half of the interval. This is a consumer
of the actual growth exponent, not membership in a candidate polygon.
-/

noncomputable section

open Expdb
open scoped NNReal

namespace TaoTrudgianYang2025

theorem exponentPairLine_reflected_le {k l α : ℝ}
    (hslope : 1/2 ≤ l-k) (hα : 1/2 ≤ α) :
    1/2-(1-α)+exponentPairLine k l (1-α) ≤ exponentPairLine k l α := by
  have h := mul_nonneg (show 0 ≤ 2*α-1 by linarith)
    (show 0 ≤ l-k-1/2 by linarith)
  unfold exponentPairLine
  nlinarith only [h]

theorem exponentPair_of_beta_bound_half {k l : ℝ}
    (htri : InExponentPairTriangle k l) (hslope : 1/2 ≤ l-k)
    (hbeta : ∀ α : ℝ≥0, (α:ℝ) ≤ 1/2 →
      exponentSumGrowthExponent α ≤ exponentPairLine k l α) :
    ExponentPair k l := by
  apply (exponentPair_iff_beta_bound htri).mpr
  intro α hα
  by_cases hhalf : (α:ℝ) ≤ 1/2
  · exact hbeta α hhalf
  · have hαNN : α ≤ 1 := by exact_mod_cast hα
    let γ : ℝ≥0 := 1-α
    have hγreal : (γ:ℝ) = 1-(α:ℝ) := NNReal.coe_sub hαNN
    have hγhalf : (γ:ℝ) ≤ 1/2 := by rw [hγreal]; linarith
    have hγ : (γ:ℝ) ≤ 1 := by linarith
    have hγNN : γ ≤ 1 := by exact_mod_cast hγ
    have hdouble : (1-γ:ℝ≥0) = α := by
      apply NNReal.coe_injective
      rw [NNReal.coe_sub hγNN,hγreal]
      norm_num
    have hrefl := exponentSumGrowthExponent_reflection hγ
    rw [hdouble] at hrefl
    calc
      exponentSumGrowthExponent α = 1/2-(γ:ℝ)+exponentSumGrowthExponent γ := hrefl
      _ ≤ 1/2-(γ:ℝ)+exponentPairLine k l γ := by linarith [hbeta γ hγhalf]
      _ ≤ exponentPairLine k l α := by
        rw [hγreal]
        exact exponentPairLine_reflected_le hslope (le_of_not_ge hhalf)

theorem exponentPair_iff_beta_bound_half {k l : ℝ}
    (htri : InExponentPairTriangle k l) (hslope : 1/2 ≤ l-k) :
    ExponentPair k l ↔ ∀ α : ℝ≥0, (α:ℝ) ≤ 1/2 →
      exponentSumGrowthExponent α ≤ exponentPairLine k l α := by
  constructor
  · intro h α hα
    exact exponentSumGrowthExponent_le_exponentPairLine_closed h α (by linarith)
  · exact exponentPair_of_beta_bound_half htri hslope

end TaoTrudgianYang2025

