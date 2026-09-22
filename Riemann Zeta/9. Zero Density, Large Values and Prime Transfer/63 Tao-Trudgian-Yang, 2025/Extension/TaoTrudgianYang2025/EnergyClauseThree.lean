import TaoTrudgianYang2025.EnergyClauseThreeGeneral
import TaoTrudgianYang2025.EnergyClauseThreeZetaCertificates
import TaoTrudgianYang2025.ZetaTwelfthMoment

/-!
# Add-est (iii) from corrected powering and the actual zeta moment

The complete short-zeta range is derived explicitly, so the proved
endpoint-one transfer suffices. No endpoint-two corollary is assumed.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem InZetaLargeValueEnergyRegion.energyClauseThree
    {σ τ ρ e s : ℝ} (h : InZetaLargeValueEnergyRegion σ τ ρ e s)
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 443/586) (htlo : 3/2 ≤ τ) (hthi : τ ≤ 2) :
    e ≤ energyClauseThreeRate σ*τ := by
  have hr := h.rho_le_of_largeValueBound
    (zetaTwelfth_short_largeValueBound (by linarith) htlo)
  obtain ⟨i,hi⟩ := exists_heathBrownNineBranch h.toGeneral.heathBrown_relation
  exact hi.trans (energyClauseThree_zeta_branch hlo hhi htlo hthi hr i)

theorem energyClauseThree_short_zeta {σ τ : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 443/586) (htlo : 1 ≤ τ) (hthi : τ ≤ 2) :
    IsZetaLargeValueEnergyBound σ τ (energyClauseThreeRate σ*τ) := by
  by_cases ht : τ < 3/2
  · exact zetaShort_energyBound_any (by linarith) htlo ht _
  · by_contra hnot
    obtain ⟨ρ,e,s,hregion,hlarge⟩ := zetaEnergyRegion_exists_rhoStar_gt_of_not_bound
      (by linarith : 1/2 ≤ σ) (by linarith : σ ≤ 1) (by linarith : 0 ≤ τ) hnot
    exact (not_lt_of_ge (hregion.energyClauseThree hlo hhi (le_of_not_gt ht) hthi)) hlarge

/-- The complete third printed clause on its exact closed interval.
No large-values, energy, or moment theorem is accepted as an input. -/
theorem energyClauseThree {σ : ℝ} (hlo : 173/229 ≤ σ) (hhi : σ ≤ 443/586) :
    IsZeroDensityEnergyBound σ (energyClauseThreeRate σ/(1-σ)) := by
  apply isZeroDensityEnergyBound_of_bounded_energy_ranges σ (energyClauseThreeRate σ) 2
    (by linarith) (by linarith) (energyClauseThreeRate_pos hlo hhi).le (by norm_num)
  · intro τ ht
    exact energyClauseThree_short_zeta hlo hhi ht.1 ht.2.le
  · intro τ ht
    exact energyClauseThree_general_bound hlo hhi ht.1 (by linarith [ht.2])

end TaoTrudgianYang2025
