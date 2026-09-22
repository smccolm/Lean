import TaoTrudgianYang2025.EnergyClauseEightGeneral
import TaoTrudgianYang2025.EnergyClauseEightZetaCertificates
import TaoTrudgianYang2025.ZetaTwelfthMoment

/-!
# Add-est (viii) from corrected powering and the actual zeta moment

The complete short-zeta range is derived explicitly, so the proved
endpoint-one transfer suffices with tau0=2. This derives both full ranges,
instead of assuming the blueprint's varying-height intermediate bounds.
The exact paper and blueprint conclusions are unchanged.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem InZetaLargeValueEnergyRegion.energyClauseEight
    {σ τ ρ e s : ℝ} (h : InZetaLargeValueEnergyRegion σ τ ρ e s)
    (hlo : 79/103 ≤ σ) (hhi : σ ≤ 84/109) (htlo : 3/2 ≤ τ) (hthi : τ ≤ 2) :
    e ≤ energyClauseEightRate σ*τ := by
  have hr := h.rho_le_of_largeValueBound
    (zetaTwelfth_short_largeValueBound (by linarith) htlo)
  obtain ⟨i,hi⟩ := exists_heathBrownNineBranch h.toGeneral.heathBrown_relation
  exact hi.trans (energyClauseEight_zeta_branch hlo hhi htlo hthi hr i)

theorem energyClauseEight_short_zeta {σ τ : ℝ}
    (hlo : 79/103 ≤ σ) (hhi : σ ≤ 84/109) (htlo : 1 ≤ τ) (hthi : τ ≤ 2) :
    IsZetaLargeValueEnergyBound σ τ (energyClauseEightRate σ*τ) := by
  by_cases ht : τ < 3/2
  · exact zetaShort_energyBound_any (by linarith) htlo ht _
  · by_contra hnot
    obtain ⟨ρ,e,s,hregion,hlarge⟩ := zetaEnergyRegion_exists_rhoStar_gt_of_not_bound
      (by linarith : 1/2 ≤ σ) (by linarith : σ ≤ 1) (by linarith : 0 ≤ τ) hnot
    exact (not_lt_of_ge (hregion.energyClauseEight hlo hhi (le_of_not_gt ht) hthi)) hlarge

/-- The complete blueprint bound on its full closed interval.
No large-values, energy, or moment theorem is accepted as an input. -/
theorem energyClauseEight {σ : ℝ} (hlo : 79/103 ≤ σ) (hhi : σ ≤ 84/109) :
    IsZeroDensityEnergyBound σ (energyClauseEightRate σ/(1-σ)) := by
  apply isZeroDensityEnergyBound_of_bounded_energy_ranges σ (energyClauseEightRate σ) 2
    (by linarith) (by linarith) (energyClauseEightRate_pos hlo hhi).le (by norm_num)
  · intro τ ht
    exact energyClauseEight_short_zeta hlo hhi ht.1 ht.2.le
  · intro τ ht
    exact energyClauseEight_general_bound hlo hhi ht.1 (by linarith [ht.2])

/-- Literal source-facing form of blueprint theorem imp-energy-bound7. -/
theorem energyClauseEight_blueprint {σ : ℝ}
    (hlo : 79/103 ≤ σ) (hhi : σ ≤ 84/109) :
    zeroDensityEnergyExponent σ ≤
      ((max ((18-19*σ)/(2*(37*σ-27)*(1-σ)))
        (5*(18-19*σ)/(2*(13*σ-3)*(1-σ))) : ℝ) : EReal) := by
  simpa only [energyClauseEightRate_div_eq_blueprint hhi] using
    zeroDensityEnergyExponent_le_of_bound (energyClauseEight hlo hhi)

end TaoTrudgianYang2025
