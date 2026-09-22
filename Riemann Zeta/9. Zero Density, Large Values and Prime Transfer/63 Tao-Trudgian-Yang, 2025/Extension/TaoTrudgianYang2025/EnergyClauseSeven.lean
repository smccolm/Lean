import TaoTrudgianYang2025.EnergyClauseSevenGeneral
import TaoTrudgianYang2025.EnergyClauseSevenZetaCertificates
import TaoTrudgianYang2025.ZetaTwelfthMoment

/-!
# Add-est (vii) from corrected powering and the actual zeta moment

The complete short-zeta range is derived explicitly, so the proved
endpoint-one transfer suffices. No endpoint-two corollary is assumed.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem InZetaLargeValueEnergyRegion.energyClauseSeven
    {σ τ ρ e s : ℝ} (h : InZetaLargeValueEnergyRegion σ τ ρ e s)
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 79/103) (htlo : 3/2 ≤ τ) (hthi : τ ≤ 2) :
    e ≤ energyClauseSevenRate σ*τ := by
  have hr := h.rho_le_of_largeValueBound
    (zetaTwelfth_short_largeValueBound (by linarith) htlo)
  obtain ⟨i,hi⟩ := exists_heathBrownNineBranch h.toGeneral.heathBrown_relation
  exact hi.trans (energyClauseSeven_zeta_branch hlo hhi htlo hthi hr i)

theorem energyClauseSeven_short_zeta {σ τ : ℝ}
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 79/103) (htlo : 1 ≤ τ) (hthi : τ ≤ 2) :
    IsZetaLargeValueEnergyBound σ τ (energyClauseSevenRate σ*τ) := by
  by_cases ht : τ < 3/2
  · exact zetaShort_energyBound_any (by linarith) htlo ht _
  · by_contra hnot
    obtain ⟨ρ,e,s,hregion,hlarge⟩ := zetaEnergyRegion_exists_rhoStar_gt_of_not_bound
      (by linarith : 1/2 ≤ σ) (by linarith : σ ≤ 1) (by linarith : 0 ≤ τ) hnot
    exact (not_lt_of_ge (hregion.energyClauseSeven hlo hhi (le_of_not_gt ht) hthi)) hlarge

/-- The complete blueprint bound on its full closed interval.
No large-values, energy, or moment theorem is accepted as an input. -/
theorem energyClauseSeven {σ : ℝ} (hlo : 42/55 ≤ σ) (hhi : σ ≤ 79/103) :
    IsZeroDensityEnergyBound σ (energyClauseSevenRate σ/(1-σ)) := by
  apply isZeroDensityEnergyBound_of_bounded_energy_ranges σ (energyClauseSevenRate σ) 2
    (by linarith) (by linarith) (energyClauseSevenRate_pos hlo hhi).le (by norm_num)
  · intro τ ht
    exact energyClauseSeven_short_zeta hlo hhi ht.1 ht.2.le
  · intro τ ht
    exact energyClauseSeven_general_bound hlo hhi ht.1 (by linarith [ht.2])

/-- Literal source-facing form of blueprint theorem imp-energy-bound6. -/
theorem energyClauseSeven_blueprint {σ : ℝ}
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 79/103) :
    zeroDensityEnergyExponent σ ≤
      ((max ((18-19*σ)/(6*(15*σ-11)*(1-σ)))
        (3*(18-19*σ)/(4*(4*σ-1)*(1-σ))) : ℝ) : EReal) := by
  simpa only [energyClauseSevenRate_div_eq_blueprint hhi] using
    zeroDensityEnergyExponent_le_of_bound (energyClauseSeven hlo hhi)

end TaoTrudgianYang2025
