import TaoTrudgianYang2025.LargeValueBoundClosure
import TaoTrudgianYang2025.LargeValueNonnegative
import TaoTrudgianYang2025.LargeValueRegionWitness
import TaoTrudgianYang2025.EnergyPoweringBounds

/-!
# Large-value powering from the corrected cardinality witness

This is the actual uniform epsilon-loss estimate. It consumes the cardinality
witness of corrected powering; neither fifth coordinate is constrained.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem IsLargeValueBound.of_powered
    {σ τ B : ℝ} (hσ : 1/2 ≤ σ) (hσ₁ : σ ≤ 1) (hτ : 0 ≤ τ)
    (k : ℕ) (hk : 1 ≤ k) (hbound : IsLargeValueBound σ (τ/k) B) :
    IsLargeValueBound σ τ (k*B) := by
  by_contra hn
  obtain ⟨ρ,e,s,hr,hlarge⟩ :=
    energyRegion_exists_rho_gt_of_not_largeValueBound hσ hσ₁ hτ hn
  obtain ⟨eCard,sCard,hpowered,_he⟩ := (hr.corrected_powering k hk).1
  have hle := hpowered.rho_le_of_largeValueBound hbound
  have hkReal : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hp := (div_le_iff₀ hkReal).mp hle
  nlinarith

theorem largeValueExponent_le_of_powered_real_bound
    {σ τ B : ℝ} (hσ : 1/2 ≤ σ) (hσ₁ : σ ≤ 1) (hτ : 0 ≤ τ)
    (k : ℕ) (hk : 1 ≤ k)
    (hbound : largeValueExponent σ (τ/k) ≤ (B:EReal)) :
    largeValueExponent σ τ ≤ ((k*B:ℝ):EReal) :=
  largeValueExponent_le_of_bound
    (IsLargeValueBound.of_powered hσ hσ₁ hτ k hk
      (isLargeValueBound_of_exponent_le hbound))

/-- The source powering inequality, including the natural zero-power endpoint. -/
theorem largeValueExponent_powering {σ τ : ℝ}
    (hσ : 1/2 ≤ σ) (hσ₁ : σ ≤ 1) (hτ : 0 ≤ τ) (k : ℕ) :
    largeValueExponent σ (k*τ) ≤ (k:EReal)*largeValueExponent σ τ := by
  by_cases hk : k = 0
  · subst k
    simp only [Nat.cast_zero,zero_mul,largeValueExponent_zero_height hσ hσ₁,le_refl]
  have hkOne : 1 ≤ k := by omega
  have hkReal : (k:ℝ) ≠ 0 := by exact_mod_cast hk
  have hfinite := largeValueExponent_coe_toReal hσ hσ₁ hτ
  have hb : largeValueExponent σ ((k:ℝ)*τ/k) ≤
      ((largeValueExponent σ τ).toReal:EReal) := by
    rw [mul_div_cancel_left₀ τ hkReal,hfinite]
  have hp := largeValueExponent_le_of_powered_real_bound hσ hσ₁
    (mul_nonneg (Nat.cast_nonneg k) hτ) k hkOne hb
  simpa only [EReal.coe_mul,EReal.coe_natCast,hfinite] using hp

/-- Bounds on the closed factor-two height interval control every larger height. -/
theorem isLargeValueBound_of_bounded_power_range
    {σ B τ₀ : ℝ} (hσ : 1/2 ≤ σ) (hσ₁ : σ ≤ 1) (hτ₀ : 0 < τ₀)
    (hbound : ∀ τ ∈ Set.Icc τ₀ (2*τ₀), IsLargeValueBound σ τ (B*τ)) :
    ∀ τ : ℝ, τ₀ ≤ τ → IsLargeValueBound σ τ (B*τ) := by
  intro τ hτ
  obtain ⟨k,hk,hmem⟩ := exists_power_height_in_Icc hτ₀ hτ
  have hp := IsLargeValueBound.of_powered hσ hσ₁ (hτ₀.trans_le hτ).le k hk
    (hbound (τ/k) hmem)
  have hkReal : (k:ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have heq : (k:ℝ)*(B*(τ/k)) = B*τ := by field_simp
  simpa only [heq] using hp

end TaoTrudgianYang2025

