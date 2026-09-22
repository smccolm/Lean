import TaoTrudgianYang2025.BourgainRegionDichotomy
import TaoTrudgianYang2025.ClassicalLargeValueRegions

/-!
# The ninth frozen Bourgain row on actual cardinality/energy regions

The logarithmic dichotomy and the cardinality side condition are both derived.
Corrected cardinality powering transports the row without scaling the fifth
coordinate or confusing the independent energy witness with this witness.
-/

noncomputable section

namespace TaoTrudgianYang2025

/-- Classical mean square supplies the row's cardinality side condition. -/
theorem InCardinalityEnergyRegion.bourgain_cardinality_le_one
    {σ τ ρ energy : ℝ} (h : InCardinalityEnergyRegion σ τ ρ energy)
    (hσ : 3/4 ≤ σ) (hτ : τ ≤ 3/2) : ρ ≤ 1 := by
  apply h.classical_cardinality.trans
  unfold classicalLargeValueExponent
  apply max_le
  · linarith
  · have hm := min_le_left (1-2*σ) (4-6*σ)
    linarith

/-- The actual source row, with no logarithmic dichotomy premise. -/
theorem InCardinalityEnergyRegion.bourgain_ninth_row
    {σ τ ρ energy : ℝ} (h : InCardinalityEnergyRegion σ τ ρ energy)
    (hσ : 3/4 < σ) (hτlo : 1 ≤ τ) (hτhi : τ ≤ 3/2)
    (hlower : 16*σ-11 ≤ τ) (hupper : 20*σ+τ/3 ≤ 16) :
    ρ ≤ 9-12*σ+2*τ/3 := by
  obtain ⟨hχ, hmargin⟩ := bourgain_ninth_row_local_height_margin hσ hlower hupper
  apply bourgain_ninth_row_of_log_dichotomy
    (h.bourgain_cardinality_le_one hσ.le hτhi) hτlo hτhi hlower hupper
  exact h.bourgain_log_dichotomy hσ hχ hmargin

/-- Apply the row to the corrected cardinality-preserving witness. -/
theorem InCardinalityEnergyRegion.bourgain_ninth_row_powered
    {σ τ ρ energy : ℝ} (h : InCardinalityEnergyRegion σ τ ρ energy)
    (q : ℕ) (hq : 1 ≤ q) (hσ : 3/4 < σ)
    (hτlo : 1 ≤ τ/q) (hτhi : τ/q ≤ 3/2)
    (hlower : 16*σ-11 ≤ τ/q) (hupper : 20*σ+(τ/q)/3 ≤ 16) :
    ρ/q ≤ 9-12*σ+2*(τ/q)/3 := by
  obtain ⟨e, he, _⟩ := (correctedCardinalityEnergyPowering _ _ _ _ q hq h).1
  exact he.bourgain_ninth_row hσ hτlo hτhi hlower hupper

end TaoTrudgianYang2025
