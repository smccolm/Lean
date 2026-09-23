import TaoTrudgianYang2025.ClassicalLargeValueRegions
import TaoTrudgianYang2025.LargeValueRegionWitness
import TaoTrudgianYang2025.LargeValuePowering

/-! Uniform Huxley bounds extracted from actual classical region witnesses. -/

namespace TaoTrudgianYang2025

theorem huxley_largeValueBound {σ τ : ℝ}
    (hσ : 1/2 ≤ σ) (hσ₁ : σ ≤ 1) (hτ : 0 ≤ τ) :
    IsLargeValueBound σ τ (max (2-2*σ) (4+τ-6*σ)) := by
  apply (isLargeValueBound_iff_region_cardinality hσ hσ₁ hτ).mpr
  intro ρ e s hr
  exact (show InCardinalityEnergyRegion σ τ ρ e from ⟨s,hr⟩).huxley_cardinality

theorem largeValueExponent_le_huxley {σ τ : ℝ}
    (hσ : 1/2 ≤ σ) (hσ₁ : σ ≤ 1) (hτ : 0 ≤ τ) :
    largeValueExponent σ τ ≤ ((max (2-2*σ) (4+τ-6*σ):ℝ):EReal) :=
  largeValueExponent_le_of_bound (huxley_largeValueBound hσ hσ₁ hτ)

theorem largeValueExponent_le_short_huxley {σ τ : ℝ}
    (hσ : 1/2 ≤ σ) (hσ₁ : σ ≤ 1) (hτ : 0 ≤ τ) (hshort : τ ≤ 4*σ-2) :
    largeValueExponent σ τ ≤ ((2-2*σ:ℝ):EReal) := by
  simpa only [max_eq_left (show 4+τ-6*σ ≤ 2-2*σ by linarith)] using
    largeValueExponent_le_huxley hσ hσ₁ hτ

theorem largeValueExponent_le_powered_huxley {σ τ : ℝ}
    (hσ : 1/2 ≤ σ) (hσ₁ : σ ≤ 1) (hτ : 0 ≤ τ) (k : ℕ) (hk : 1 ≤ k) :
    largeValueExponent σ τ ≤
      ((k*max (2-2*σ) (4+τ/k-6*σ):ℝ):EReal) :=
  largeValueExponent_le_of_powered_real_bound hσ hσ₁ hτ k hk
    (largeValueExponent_le_huxley hσ hσ₁ (div_nonneg hτ (Nat.cast_nonneg _)))

end TaoTrudgianYang2025

