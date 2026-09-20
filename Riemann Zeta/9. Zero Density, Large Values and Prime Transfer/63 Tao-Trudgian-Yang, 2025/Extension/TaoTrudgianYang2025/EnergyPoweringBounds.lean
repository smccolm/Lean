import TaoTrudgianYang2025.CorrectedEnergyPowering

/-!
# Energy bounds from corrected powering

The proved energy witness transfers uniform epsilon-loss bounds and reduces
the unbounded general-height range to one compact factor-two interval.
The separate short-zeta-height reduction to the printed endpoint two is
not asserted here.
-/

noncomputable section

namespace TaoTrudgianYang2025

/-- A uniform energy bound at the powered height implies a uniform bound
at the original height. Compactness supplies all epsilon-loss uniformity. -/
theorem IsLargeValueEnergyBound.of_powered
    {σ τ B : ℝ} (hσLower : 1 / 2 ≤ σ) (hσUpper : σ ≤ 1) (hτ : 0 ≤ τ)
    (k : ℕ) (hk : 1 ≤ k) (hbound : IsLargeValueEnergyBound σ (τ / k) B) :
    IsLargeValueEnergyBound σ τ (k * B) := by
  by_contra hnot
  obtain ⟨ρ, energy, s, hregion, hlarge⟩ :=
    energyRegion_exists_rhoStar_gt_of_not_bound hσLower hσUpper hτ hnot
  obtain ⟨card, sum, hpowered, _hcard⟩ := (hregion.corrected_powering k hk).2
  have hle := hpowered.rhoStar_le_of_energyBound hbound
  have hkReal : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have he := (div_le_iff₀ hkReal).mp hle
  nlinarith

/-- An actual upper bound for the energy exponent at a powered height
transfers to the original height, including the epsilon-loss boundary. -/
theorem largeValueEnergyExponent_le_of_powered_real_bound
    {σ τ B : ℝ} (hσLower : 1 / 2 ≤ σ) (hσUpper : σ ≤ 1) (hτ : 0 ≤ τ)
    (k : ℕ) (hk : 1 ≤ k)
    (hbound : largeValueEnergyExponent σ (τ / k) ≤ (B : EReal)) :
    largeValueEnergyExponent σ τ ≤ ((k * B : ℝ) : EReal) := by
  apply largeValueEnergyExponent_le_of_bound
  apply IsLargeValueEnergyBound.of_powered hσLower hσUpper hτ k hk
  exact isLargeValueEnergyBound_of_exponent_le hσLower hσUpper
    (div_nonneg hτ (Nat.cast_nonneg _)) hbound

/-- Every height above a positive cutoff can be divided by a positive
integer into the closed factor-two interval starting at that cutoff. -/
theorem exists_power_height_in_Icc
    {τ₀ τ : ℝ} (hτ₀ : 0 < τ₀) (hτ : τ₀ ≤ τ) :
    ∃ k : ℕ, 1 ≤ k ∧ τ / k ∈ Set.Icc τ₀ (2 * τ₀) := by
  let k : ℕ := ⌊τ / τ₀⌋₊
  have hratio : 1 ≤ τ / τ₀ := (le_div_iff₀ hτ₀).2 (by simpa using hτ)
  have hk : 1 ≤ k := (Nat.one_le_floor_iff _).2 hratio
  have hkReal : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkOne : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hlo : (k : ℝ) ≤ τ / τ₀ := Nat.floor_le (zero_le_one.trans hratio)
  have hhi : τ / τ₀ < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  refine ⟨k, hk, ?_, ?_⟩
  · apply (le_div_iff₀ hkReal).2
    have := (le_div_iff₀ hτ₀).1 hlo
    nlinarith
  · apply (div_le_iff₀ hkReal).2
    have := (div_lt_iff₀ hτ₀).1 hhi
    nlinarith

/-- The compact general-energy interval controls the whole upper-height
range. This consumes the full corrected powering theorem, not an assumed
closure rule for a region or polytope. -/
theorem isLargeValueEnergyBound_of_bounded_power_range
    {σ B τ₀ : ℝ} (hσLower : 1 / 2 ≤ σ) (hσUpper : σ ≤ 1) (hτ₀ : 0 < τ₀)
    (hbound : ∀ τ ∈ Set.Icc τ₀ (2 * τ₀), IsLargeValueEnergyBound σ τ (B * τ)) :
    ∀ τ : ℝ, τ₀ ≤ τ → IsLargeValueEnergyBound σ τ (B * τ) := by
  intro τ hτ
  obtain ⟨k, hk, hmem⟩ := exists_power_height_in_Icc hτ₀ hτ
  have hp := IsLargeValueEnergyBound.of_powered hσLower hσUpper
    (hτ₀.trans_le hτ).le k hk (hbound (τ / k) hmem)
  have hkReal : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have heq : (k : ℝ) * (B * (τ / k)) = B * τ := by field_simp
  simpa only [heq] using hp

/-- Compact-range transfer with the already proved zeta endpoint one.
The source corollary's stronger lower endpoint two still requires its
separate short-height argument. -/
theorem isZeroDensityEnergyBound_of_bounded_energy_ranges
    (σ B τ₀ : ℝ) (hσ : 1 / 2 < σ) (hσUpper : σ < 1)
    (hB : 0 ≤ B) (hτ₀ : 0 < τ₀)
    (hZeta : ∀ τ ∈ Set.Ico (1 : ℝ) τ₀, IsZetaLargeValueEnergyBound σ τ (B * τ))
    (hGeneral : ∀ τ ∈ Set.Icc τ₀ (2 * τ₀), IsLargeValueEnergyBound σ τ (B * τ)) :
    IsZeroDensityEnergyBound σ (B / (1 - σ)) := by
  have hg := isLargeValueEnergyBound_of_bounded_power_range hσ.le hσUpper.le hτ₀ hGeneral
  apply isZeroDensityEnergyBound_of_uniform_energy_bounds σ B τ₀ hσ hσUpper hB hτ₀ _ hg
  intro τ hτ
  by_cases ht : τ < τ₀
  · exact hZeta τ ⟨hτ, ht⟩
  · exact (hg τ (le_of_not_gt ht)).toZeta

end TaoTrudgianYang2025
