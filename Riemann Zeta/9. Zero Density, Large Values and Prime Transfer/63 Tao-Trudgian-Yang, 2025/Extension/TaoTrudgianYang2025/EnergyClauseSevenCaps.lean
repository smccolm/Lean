import TaoTrudgianYang2025.JutilaEnergyRegions
import TaoTrudgianYang2025.EnergyClauseTwoCaps

/-!
# Actual corrected-powering cardinality caps for Add-est (vii)

Jutila's integer is six. Cardinality witnesses at q and q+1 are
independent of the energy witness; no fifth coordinate is scaled.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem jutila_six_formula (σ t : ℝ) :
    jutilaLargeValueExponent 6 σ t =
      max (2-2*σ) (max (t+11/3-(17/3)*σ) (t+36-48*σ)) := by
  unfold jutilaLargeValueExponent
  norm_num
  congr 2 <;> ring

theorem InCardinalityEnergyRegion.jutila_six_cardinality_powered
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (q : ℕ) (hq : 1 ≤ q) :
    ρ/q ≤ max (2-2*σ) (max (τ/q+11/3-(17/3)*σ) (τ/q+36-48*σ)) := by
  simpa only [jutila_six_formula] using
    h.jutila_cardinality_powered q 6 hq (by norm_num)

theorem jutila_six_low_sigma {σ t : ℝ} (hσ : σ ≤ 97/127) :
    max (2-2*σ) (max (t+11/3-(17/3)*σ) (t+36-48*σ)) =
      max (2-2*σ) (t+36-48*σ) := by
  rw [max_eq_right (by linarith : t+11/3-(17/3)*σ ≤ t+36-48*σ)]

theorem jutila_six_high_sigma {σ t : ℝ} (hσ : 97/127 ≤ σ) :
    max (2-2*σ) (max (t+11/3-(17/3)*σ) (t+36-48*σ)) =
      max (2-2*σ) (t+11/3-(17/3)*σ) := by
  rw [max_eq_left (by linarith : t+36-48*σ ≤ t+11/3-(17/3)*σ)]

theorem jutila_six_at_most_one {σ t : ℝ}
    (hσ : 42/55 ≤ σ) (ht : t ≤ 1) :
    max (2-2*σ) (max (t+11/3-(17/3)*σ) (t+36-48*σ)) = 2-2*σ := by
  apply max_eq_left
  apply max_le <;> linarith

theorem InCardinalityEnergyRegion.energyClauseSeven_cardinality_caps
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 79/103)
    (q : ℕ) (hq : q=2 ∨ q=3) (htlo : (q : ℝ) ≤ τ) (hthi : τ ≤ q+1) :
    1 ≤ τ/q ∧ τ/q ≤ 3/2 ∧
      ρ/q ≤ max (2-2*σ) (max (τ/q+11/3-(17/3)*σ) (τ/q+36-48*σ)) ∧
      ρ/q ≤ 3-3*σ := by
  have hqNat : 1 ≤ q := by rcases hq with rfl|rfl <;> omega
  have htone : 1 ≤ τ/q := by
    rcases hq with rfl|rfl <;> norm_num at * <;> linarith
  have htthree : τ/q ≤ 3/2 := by
    rcases hq with rfl|rfl <;> norm_num at * <;> linarith
  have hj := h.jutila_six_cardinality_powered q hqNat
  have hplus := h.jutila_six_cardinality_powered (q+1) (by omega)
  push_cast at hplus
  have htplus : τ/(q+1) ≤ 1 :=
    (div_le_iff₀ (by positivity : (0 : ℝ) < q+1)).2 (by simpa using hthi)
  rw [jutila_six_at_most_one hlo htplus] at hplus
  have hcap : ρ/q ≤ 3-3*σ := by
    rcases hq with rfl|rfl <;> norm_num at * <;> linarith
  exact ⟨htone,htthree,hj,hcap⟩

end TaoTrudgianYang2025
