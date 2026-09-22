import TaoTrudgianYang2025.EnergyClauseNineGeneral
import TaoTrudgianYang2025.EnergyClauseNineZeta

/-!
# Add-est (ix) from the corrected two-witness repair

The source rate and full closed sigma interval are unchanged.
All general and zeta input ranges are proved, not assumed.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem energyClauseNine {σ : ℝ} (hlo : 84/109 ≤ σ) (hhi : σ ≤ 5/6) :
    IsZeroDensityEnergyBound σ (energyClauseNineRate σ/(1-σ)) := by
  apply isZeroDensityEnergyBound_of_bounded_energy_ranges σ
    (energyClauseNineRate σ) (8*σ-4) (by linarith) (by linarith)
    (energyClauseNineRate_pos hlo hhi).le (by linarith)
  · intro τ ht
    exact energyClauseNine_zeta_bound hlo hhi ht.1 ht.2.le
  · intro τ ht
    exact energyClauseNine_general_bound hlo hhi ht.1 ht.2

theorem energyClauseNine_blueprint {σ : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 5/6) :
    zeroDensityEnergyExponent σ ≤
      ((max ((18-19*σ)/(9*(3*σ-2)*(1-σ)))
        (4*(10-9*σ)/(5*(4*σ-1)*(1-σ))) : ℝ) : EReal) := by
  simpa only [energyClauseNineRate_div_eq_blueprint hhi] using
    zeroDensityEnergyExponent_le_of_bound (energyClauseNine hlo hhi)

end TaoTrudgianYang2025
