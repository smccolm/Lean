import TaoTrudgianYang2025.JutilaEnergyRegions
import TaoTrudgianYang2025.EnergyClauseTwoCaps

/-!
# Actual corrected-powering cardinality caps for Add-est (vi)

The full blueprint domain is retained. Jutila's integer is ten. Independent cardinality witnesses at q
and q+1 supply the two caps; no fifth-coordinate scaling is asserted.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem jutila_ten_formula (σ t : ℝ) :
    jutilaLargeValueExponent 10 σ t =
      max (2-2*σ) (max (t+19/5-(29/5)*σ) (t+60-80*σ)) := by
  unfold jutilaLargeValueExponent
  norm_num
  congr 2 <;> ring

theorem InCardinalityEnergyRegion.jutila_ten_cardinality_powered
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (q : ℕ) (hq : 1 ≤ q) :
    ρ/q ≤ max (2-2*σ) (max (τ/q+19/5-(29/5)*σ) (τ/q+60-80*σ)) := by
  simpa only [jutila_ten_formula] using
    h.jutila_cardinality_powered q 10 hq (by norm_num)

theorem jutila_ten_low_sigma {σ t : ℝ} (hσ : σ ≤ 281/371) :
    max (2-2*σ) (max (t+19/5-(29/5)*σ) (t+60-80*σ)) =
      max (2-2*σ) (t+60-80*σ) := by
  rw [max_eq_right (by linarith : t+19/5-(29/5)*σ ≤ t+60-80*σ)]

theorem jutila_ten_high_sigma {σ t : ℝ} (hσ : 281/371 ≤ σ) :
    max (2-2*σ) (max (t+19/5-(29/5)*σ) (t+60-80*σ)) =
      max (2-2*σ) (t+19/5-(29/5)*σ) := by
  rw [max_eq_left (by linarith : t+60-80*σ ≤ t+19/5-(29/5)*σ)]

theorem jutila_ten_at_most_one {σ t : ℝ}
    (hσ : 664/877 ≤ σ) (ht : t ≤ 1) :
    max (2-2*σ) (max (t+19/5-(29/5)*σ) (t+60-80*σ)) = 2-2*σ := by
  apply max_eq_left
  apply max_le <;> linarith

theorem InCardinalityEnergyRegion.energyClauseSix_cardinality_caps
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 31/40)
    (q : ℕ) (hq : q=2 ∨ q=3) (htlo : (q : ℝ) ≤ τ) (hthi : τ ≤ q+1) :
    1 ≤ τ/q ∧ τ/q ≤ 3/2 ∧
      ρ/q ≤ max (2-2*σ) (max (τ/q+19/5-(29/5)*σ) (τ/q+60-80*σ)) ∧
      ρ/q ≤ max (18/5-4*σ) (12/5-4*σ+τ/q) ∧
      ρ/q ≤ 3-3*σ := by
  have hqNat : 1 ≤ q := by rcases hq with rfl|rfl <;> omega
  obtain ⟨htone,htthree,_,hg,_⟩ :=
    h.energyClauseTwo_cardinality_caps (by linarith) q hq htlo hthi
  have hj := h.jutila_ten_cardinality_powered q hqNat
  have hplus := h.jutila_ten_cardinality_powered (q+1) (by omega)
  push_cast at hplus
  have htplus : τ/(q+1) ≤ 1 :=
    (div_le_iff₀ (by positivity : (0 : ℝ) < q+1)).2 (by simpa using hthi)
  rw [jutila_ten_at_most_one hlo htplus] at hplus
  have hcap : ρ/q ≤ 3-3*σ := by
    rcases hq with rfl|rfl <;> norm_num at * <;> linarith
  exact ⟨htone,htthree,hj,hg,hcap⟩

end TaoTrudgianYang2025
