import TaoTrudgianYang2025.EnergyCardinalityBounds
import TaoTrudgianYang2025.EnergyPoweringObstruction

/-!
# Nonnegative finite large-value exponents and the exact zero-height endpoint

The lower bound uses the genuine singleton pattern that also witnesses the
permanent obstruction. Its source and counterexample are not modified.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem IsLargeValueBound.nonneg {σ τ B : ℝ}
    (h : IsLargeValueBound σ τ B) (hσ : 1/2 ≤ σ) (hσ₁ : σ ≤ 1) (hτ : 0 ≤ τ) :
    0 ≤ B :=
  (singleton_mem_largeValueEnergyRegion σ τ hσ hσ₁ hτ).rho_le_of_largeValueBound h

theorem largeValueExponent_nonneg {σ τ : ℝ}
    (hσ : 1/2 ≤ σ) (hσ₁ : σ ≤ 1) (hτ : 0 ≤ τ) :
    0 ≤ largeValueExponent σ τ := by
  unfold largeValueExponent
  apply le_sInf
  rintro x ⟨B,hB,rfl⟩
  exact EReal.coe_nonneg.mpr (IsLargeValueBound.nonneg hB hσ hσ₁ hτ)

theorem largeValueExponent_zero_height {σ : ℝ} (hσ : 1/2 ≤ σ) (hσ₁ : σ ≤ 1) :
    largeValueExponent σ 0 = 0 :=
  le_antisymm (by simpa using largeValueExponent_le_tau σ (le_refl 0))
    (largeValueExponent_nonneg hσ hσ₁ (le_refl 0))

theorem largeValueExponent_coe_toReal {σ τ : ℝ}
    (hσ : 1/2 ≤ σ) (hσ₁ : σ ≤ 1) (hτ : 0 ≤ τ) :
    ((largeValueExponent σ τ).toReal:EReal) = largeValueExponent σ τ := by
  apply EReal.coe_toReal
  · exact ne_top_of_le_ne_top (EReal.coe_ne_top τ) (largeValueExponent_le_tau σ hτ)
  · exact ne_bot_of_le_ne_bot EReal.zero_ne_bot (largeValueExponent_nonneg hσ hσ₁ hτ)

end TaoTrudgianYang2025

