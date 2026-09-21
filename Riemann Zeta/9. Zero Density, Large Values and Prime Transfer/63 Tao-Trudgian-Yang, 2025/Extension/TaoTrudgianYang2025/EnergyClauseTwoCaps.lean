import TaoTrudgianYang2025.EnergyCardinalityBounds
import TaoTrudgianYang2025.HeathBrownNineBranches

/-!
# Actual powered cardinality caps for Add-est (ii)

The middle power is two or three; an additional cardinality witness at
power k+1 supplies the cap. Every coordinate is tied to the original
realizing region point.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem energyClauseTwo_power_cover {τ : ℝ} (hlo : 2 ≤ τ) (hhi : τ ≤ 4) :
    ∃ k : ℕ, (k=2 ∨ k=3) ∧ (k:ℝ) ≤ τ ∧ τ ≤ k+1 := by
  by_cases ht : τ ≤ 3
  · exact ⟨2,Or.inl rfl,by norm_num; exact hlo,by norm_num; exact ht⟩
  · exact ⟨3,Or.inr rfl,by norm_num; linarith,by norm_num; exact hhi⟩

theorem InCardinalityEnergyRegion.energyClauseTwo_cardinality_caps
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (hσ : σ ≤ 4/5) (k : ℕ) (hk : k=2 ∨ k=3)
    (htlo : (k:ℝ) ≤ τ) (hthi : τ ≤ k+1) :
    1 ≤ τ/k ∧ τ/k ≤ 3/2 ∧
      ρ/k ≤ 1-2*σ+τ/k ∧
      ρ/k ≤ max (18/5-4*σ) (12/5-4*σ+τ/k) ∧
      ρ/k ≤ 3-3*σ := by
  have hkNat : 1 ≤ k := by rcases hk with rfl|rfl <;> omega
  have hkpos : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have htone : 1 ≤ τ/k := (le_div_iff₀ hkpos).2 (by simpa using htlo)
  have htthree : τ/k ≤ 3/2 := by
    rcases hk with rfl|rfl <;> norm_num at * <;> linarith
  have hm := h.mean_square_cardinality_powered k hkNat
  rw [max_eq_right (by linarith : 2-2*σ ≤ 1-2*σ+τ/k)] at hm
  have hg := h.guthMaynard_cardinality_powered k hkNat
  have hbase : 2-2*σ ≤ max (18/5-4*σ) (τ/k+12/5-4*σ) :=
    (by linarith : 2-2*σ ≤ 18/5-4*σ).trans (le_max_left _ _)
  rw [guthMaynardLargeValueExponent,max_eq_right hbase] at hg
  have hg' : ρ/k ≤ max (18/5-4*σ) (12/5-4*σ+τ/k) := by
    have heq : τ/k+12/5-4*σ = 12/5-4*σ+τ/k := by ring
    simpa only [heq] using hg
  have hplus := h.mean_square_cardinality_powered (k+1) (by omega)
  have hkplus : (0:ℝ) < k+1 := by positivity
  have htplus : τ/(k+1) ≤ 1 := (div_le_iff₀ hkplus).2 (by simpa using hthi)
  push_cast at hplus
  rw [max_eq_left (by linarith : 1-2*σ+τ/(k+1) ≤ 2-2*σ)] at hplus
  have hσone : σ ≤ 1 := by obtain ⟨s,hs⟩ := h; exact hs.2.1
  have hcap : ρ/k ≤ 3-3*σ := by
    rcases hk with rfl|rfl <;> norm_num at * <;> linarith
  exact ⟨htone,htthree,hm,hg',hcap⟩

end TaoTrudgianYang2025
