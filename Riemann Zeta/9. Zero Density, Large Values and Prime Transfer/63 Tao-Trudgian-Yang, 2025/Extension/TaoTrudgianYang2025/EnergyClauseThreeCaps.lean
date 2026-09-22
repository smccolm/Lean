import TaoTrudgianYang2025.JutilaEnergyRegions
import TaoTrudgianYang2025.EnergyClauseTwoCaps

/-!
# Actual corrected-powering cardinality caps for Add-est (iii)

Jutila's integer is thirteen. The independent pattern powers are q and
q+1; neither is a fifth-coordinate scaling or an energy-preserving cap.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem jutila_thirteen_low_sigma {σ t : ℝ} (hσ : σ ≤ 241/319) :
    max (2-2*σ) (max (t+50/13-(76/13)*σ) (t+78-104*σ)) =
      max (2-2*σ) (t+78-104*σ) := by
  rw [max_eq_right (by linarith : t+50/13-(76/13)*σ ≤ t+78-104*σ)]

theorem jutila_thirteen_high_sigma {σ t : ℝ} (hσ : 241/319 ≤ σ) :
    max (2-2*σ) (max (t+50/13-(76/13)*σ) (t+78-104*σ)) =
      max (2-2*σ) (t+50/13-(76/13)*σ) := by
  rw [max_eq_left (by linarith : t+78-104*σ ≤ t+50/13-(76/13)*σ)]

theorem jutila_thirteen_at_most_one {σ t : ℝ}
    (hσ : 173/229 ≤ σ) (ht : t ≤ 1) :
    max (2-2*σ) (max (t+50/13-(76/13)*σ) (t+78-104*σ)) = 2-2*σ := by
  apply max_eq_left
  apply max_le <;> linarith

/-- Both Jutila applications consume their actual cardinality witnesses.
The companion power supplies the constant cap used at large local height. -/
theorem InCardinalityEnergyRegion.energyClauseThree_cardinality_caps
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 443/586)
    (q : ℕ) (hq : q=2 ∨ q=3) (htlo : (q : ℝ) ≤ τ) (hthi : τ ≤ q+1) :
    1 ≤ τ/q ∧ τ/q ≤ 3/2 ∧
      ρ/q ≤ max (2-2*σ) (max (τ/q+50/13-(76/13)*σ) (τ/q+78-104*σ)) ∧
      ρ/q ≤ max (18/5-4*σ) (12/5-4*σ+τ/q) ∧
      ρ/q ≤ 3-3*σ := by
  have hqNat : 1 ≤ q := by rcases hq with rfl|rfl <;> omega
  obtain ⟨htone,htthree,_,hg,_⟩ :=
    h.energyClauseTwo_cardinality_caps (by linarith) q hq htlo hthi
  have hj := h.jutila_thirteen_cardinality_powered q hqNat
  have hplus := h.jutila_thirteen_cardinality_powered (q+1) (by omega)
  push_cast at hplus
  have htplus : τ/(q+1) ≤ 1 :=
    (div_le_iff₀ (by positivity : (0 : ℝ) < q+1)).2 (by simpa using hthi)
  rw [jutila_thirteen_at_most_one hlo htplus] at hplus
  have hcap : ρ/q ≤ 3-3*σ := by
    rcases hq with rfl|rfl <;> norm_num at * <;> linarith
  exact ⟨htone,htthree,hj,hg,hcap⟩

end TaoTrudgianYang2025
