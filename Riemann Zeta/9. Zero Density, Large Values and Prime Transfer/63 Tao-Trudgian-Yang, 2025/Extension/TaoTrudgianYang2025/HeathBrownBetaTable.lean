import TaoTrudgianYang2025.HeathBrownDerivative
import TaoTrudgianYang2025.BetaClosedDuality

/-!
# The Heath--Brown rows of the source beta table

The first two rows are analytic consequences of the native derivative
theorem, not merely rational identities. Both joining endpoints are
included; alpha zero uses the proved exact beta endpoint.
-/

noncomputable section

open Expdb
open scoped NNReal

namespace TaoTrudgianYang2025

theorem heathBrownBetaBound_five_first {α : ℝ}
    (hα : α ≤ 1/4) :
    heathBrownBetaBound 5 α = 1/20+3/4*α := by
  rw [heathBrownBetaBound_eq_max (by norm_num : 3 ≤ (5 : ℕ))]
  norm_num [heathBrownDerivativeExponent,heathBrownInverseExponent]
  have hfirst : max (α*(19/20)) (α-1/50) ≤ 1/20+α*(3/4) :=
    max_le (by linarith) (by linarith)
  rw [max_eq_left hfirst]
  ring

theorem heathBrownBetaBound_five_second {α : ℝ}
    (hα : 1/4 ≤ α) (hα₁ : α ≤ 2/5) :
    heathBrownBetaBound 5 α = 19/20*α := by
  rw [heathBrownBetaBound_eq_max (by norm_num : 3 ≤ (5 : ℕ))]
  norm_num [heathBrownDerivativeExponent,heathBrownInverseExponent]
  rw [max_eq_left (by linarith : α-1/50 ≤ α*(19/20))]
  rw [max_eq_right (by linarith : 1/20+α*(3/4) ≤ α*(19/20))]
  ring

theorem exponentSumGrowthExponent_le_heathBrown_firstRow
    {α : ℝ≥0} (hα : (α : ℝ) ≤ 1/4) :
    exponentSumGrowthExponent α ≤ 1/20+3/4*(α : ℝ) := by
  by_cases hpos : 0 < (α : ℝ)
  · have h := exponentSumGrowthExponent_le_heathBrown_of_derivative
      GafniTao.heathBrownKthDerivativeTheorem_native
      (by norm_num : 3 ≤ (5 : ℕ)) hpos
    rw [heathBrownBetaBound_five_first hα] at h
    exact h
  · have hz : α = 0 := NNReal.coe_injective (le_antisymm (le_of_not_gt hpos) α.coe_nonneg)
    subst α
    rw [exponentSumGrowthExponent_zero]
    norm_num

theorem exponentSumGrowthExponent_le_heathBrown_secondSegment
    {α : ℝ≥0} (hα : 1/4 ≤ (α : ℝ)) (hα₁ : (α : ℝ) ≤ 2/5) :
    exponentSumGrowthExponent α ≤ 19/20*(α : ℝ) := by
  have h := exponentSumGrowthExponent_le_heathBrown_of_derivative
    GafniTao.heathBrownKthDerivativeTheorem_native
    (by norm_num : 3 ≤ (5 : ℕ)) (by linarith : 0 < (α : ℝ))
  rw [heathBrownBetaBound_five_second hα hα₁] at h
  exact h

theorem exponentSumGrowthExponent_le_heathBrown_secondRow
    {α : ℝ≥0} (hα : 1/4 ≤ (α : ℝ)) (hα₁ : (α : ℝ) ≤ 890/3277) :
    exponentSumGrowthExponent α ≤ 19/20*(α : ℝ) :=
  exponentSumGrowthExponent_le_heathBrown_secondSegment hα (by linarith)

end TaoTrudgianYang2025
