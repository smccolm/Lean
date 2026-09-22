import TaoTrudgianYang2025.JutilaEnergyRegions
import TaoTrudgianYang2025.EnergyClauseTwoCaps

/-!
# Actual corrected-powering cardinality caps for Add-est (iv)

Jutila's integer is twelve. Independent cardinality witnesses at q
and q+1 supply the two caps; no fifth-coordinate scaling is asserted.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem jutila_twelve_formula (σ t : ℝ) :
    jutilaLargeValueExponent 12 σ t =
      max (2-2*σ) (max (t+23/6-(35/6)*σ) (t+72-96*σ)) := by
  unfold jutilaLargeValueExponent
  norm_num
  congr 2 <;> ring

theorem InCardinalityEnergyRegion.jutila_twelve_cardinality_powered
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (q : ℕ) (hq : 1 ≤ q) :
    ρ/q ≤ max (2-2*σ) (max (τ/q+23/6-(35/6)*σ) (τ/q+72-96*σ)) := by
  simpa only [jutila_twelve_formula] using
    h.jutila_cardinality_powered q 12 hq (by norm_num)

theorem jutila_twelve_low_sigma {σ t : ℝ} (hσ : σ ≤ 409/541) :
    max (2-2*σ) (max (t+23/6-(35/6)*σ) (t+72-96*σ)) =
      max (2-2*σ) (t+72-96*σ) := by
  rw [max_eq_right (by linarith : t+23/6-(35/6)*σ ≤ t+72-96*σ)]

theorem jutila_twelve_high_sigma {σ t : ℝ} (hσ : 409/541 ≤ σ) :
    max (2-2*σ) (max (t+23/6-(35/6)*σ) (t+72-96*σ)) =
      max (2-2*σ) (t+23/6-(35/6)*σ) := by
  rw [max_eq_left (by linarith : t+72-96*σ ≤ t+23/6-(35/6)*σ)]

theorem jutila_twelve_at_most_one {σ t : ℝ}
    (hσ : 443/586 ≤ σ) (ht : t ≤ 1) :
    max (2-2*σ) (max (t+23/6-(35/6)*σ) (t+72-96*σ)) = 2-2*σ := by
  apply max_eq_left
  apply max_le <;> linarith

theorem InCardinalityEnergyRegion.energyClauseFour_cardinality_caps
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 373/493)
    (q : ℕ) (hq : q=2 ∨ q=3) (htlo : (q : ℝ) ≤ τ) (hthi : τ ≤ q+1) :
    1 ≤ τ/q ∧ τ/q ≤ 3/2 ∧
      ρ/q ≤ max (2-2*σ) (max (τ/q+23/6-(35/6)*σ) (τ/q+72-96*σ)) ∧
      ρ/q ≤ max (18/5-4*σ) (12/5-4*σ+τ/q) ∧
      ρ/q ≤ 3-3*σ := by
  have hqNat : 1 ≤ q := by rcases hq with rfl|rfl <;> omega
  obtain ⟨htone,htthree,_,hg,_⟩ :=
    h.energyClauseTwo_cardinality_caps (by linarith) q hq htlo hthi
  have hj := h.jutila_twelve_cardinality_powered q hqNat
  have hplus := h.jutila_twelve_cardinality_powered (q+1) (by omega)
  push_cast at hplus
  have htplus : τ/(q+1) ≤ 1 :=
    (div_le_iff₀ (by positivity : (0 : ℝ) < q+1)).2 (by simpa using hthi)
  rw [jutila_twelve_at_most_one hlo htplus] at hplus
  have hcap : ρ/q ≤ 3-3*σ := by
    rcases hq with rfl|rfl <;> norm_num at * <;> linarith
  exact ⟨htone,htthree,hj,hg,hcap⟩

end TaoTrudgianYang2025
