import TaoTrudgianYang2025.LargeValueLowerBound
import TaoTrudgianYang2025.LargeValueElementaryBounds
import TaoTrudgianYang2025.LargeValueHuxleyBound

/-! Exact source elementary large-value calculus and its known equality ranges. -/

namespace TaoTrudgianYang2025

theorem largeValueExponent_eq_tau_small {σ τ : ℝ}
    (hσ : 1/2 ≤ σ) (hσ₁ : σ ≤ 1) (hτ : 0 ≤ τ) (hsmall : τ ≤ 2-2*σ) :
    largeValueExponent σ τ = (τ:EReal) := by
  apply le_antisymm (largeValueExponent_le_tau σ hτ)
  simpa only [min_eq_right hsmall] using largeValueExponent_lower hσ hσ₁ hτ

theorem largeValueExponent_eq_min_meanSquare {σ τ : ℝ}
    (hσ : 1/2 ≤ σ) (hσ₁ : σ ≤ 1) (hτ : 0 ≤ τ) (hτ₁ : τ ≤ 1) :
    largeValueExponent σ τ = ((min (2-2*σ) τ:ℝ):EReal) := by
  apply le_antisymm _ (largeValueExponent_lower hσ hσ₁ hτ)
  by_cases ht : 2-2*σ ≤ τ
  · rw [min_eq_left ht]
    exact largeValueExponent_le_short_meanSquare (by linarith) hτ₁
  · rw [min_eq_right (le_of_not_ge ht)]
    exact largeValueExponent_le_tau σ hτ

theorem largeValueExponent_eq_min_huxley {σ τ : ℝ}
    (hσ : 1/2 ≤ σ) (hσ₁ : σ ≤ 1) (hτ : 0 ≤ τ) (hshort : τ ≤ 4*σ-2) :
    largeValueExponent σ τ = ((min (2-2*σ) τ:ℝ):EReal) := by
  apply le_antisymm _ (largeValueExponent_lower hσ hσ₁ hτ)
  by_cases ht : 2-2*σ ≤ τ
  · rw [min_eq_left ht]
    exact largeValueExponent_le_short_huxley hσ hσ₁ hτ hshort
  · rw [min_eq_right (le_of_not_ge ht)]
    exact largeValueExponent_le_tau σ hτ

theorem largeValueExponent_one {τ : ℝ} (hτ : 0 ≤ τ) :
    largeValueExponent 1 τ = 0 := by
  by_cases ht : τ ≤ 1
  · exact largeValueExponent_one_short hτ ht
  have hlocal : ∀ t ∈ Set.Icc (1:ℝ) 2, IsLargeValueBound 1 t (0*t) := by
    intro t ht
    apply isLargeValueBound_of_exponent_le
    have h := largeValueExponent_le_short_huxley (σ:=1) (τ:=t) (by norm_num)
      (by norm_num) (by linarith [ht.1]) (by linarith [ht.2])
    norm_num at h ⊢
    exact h
  have hp := isLargeValueBound_of_bounded_power_range (τ₀:=1) (B:=0)
    (by norm_num : (1:ℝ)/2 ≤ 1) (by norm_num) (by norm_num)
    (by simpa only [mul_one] using hlocal) τ (le_of_not_ge ht)
  apply le_antisymm
  · simpa only [zero_mul,EReal.coe_zero] using largeValueExponent_le_of_bound hp
  · exact largeValueExponent_nonneg (by norm_num) (by norm_num) hτ

end TaoTrudgianYang2025
