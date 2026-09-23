import TaoTrudgianYang2025.ClassicalMeanSquareBound
import TaoTrudgianYang2025.LargeValuePowering
import TaoTrudgianYang2025.LargeValueSubdivisionBounds

/-! Source-facing mean-square bounds and their endpoint consequences. -/

namespace TaoTrudgianYang2025

theorem largeValueExponent_le_meanSquare {σ τ : ℝ} (hσ : 0 < σ) :
    largeValueExponent σ τ ≤ ((max (2-2*σ) (1+τ-2*σ):ℝ):EReal) :=
  largeValueExponent_le_of_bound (meanSquare_largeValueBound hσ)

theorem largeValueExponent_le_short_meanSquare {σ τ : ℝ}
    (hσ : 0 < σ) (hτ : τ ≤ 1) :
    largeValueExponent σ τ ≤ ((2-2*σ:ℝ):EReal) := by
  simpa only [max_eq_left (show 1+τ-2*σ ≤ 2-2*σ by linarith)] using
    largeValueExponent_le_meanSquare (τ:=τ) hσ

theorem largeValueExponent_one_short {τ : ℝ} (hτ : 0 ≤ τ) (hτ₁ : τ ≤ 1) :
    largeValueExponent 1 τ = 0 := by
  apply le_antisymm
  · have h := largeValueExponent_le_short_meanSquare (σ:=1) (by norm_num) hτ₁
    norm_num at h ⊢
    exact h
  · exact largeValueExponent_nonneg (by norm_num) (by norm_num) hτ

end TaoTrudgianYang2025

