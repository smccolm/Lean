import TaoTrudgianYang2025.EnergyClauseFourGeneral
import TaoTrudgianYang2025.EnergyClauseFourZetaCertificates
import TaoTrudgianYang2025.ZetaTwelfthMoment

/-!
# Add-est (iv) from corrected powering and the actual zeta moment

The complete short-zeta range is derived explicitly, so the proved
endpoint-one transfer suffices. No endpoint-two corollary is assumed.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem InZetaLargeValueEnergyRegion.energyClauseFour
    {σ τ ρ e s : ℝ} (h : InZetaLargeValueEnergyRegion σ τ ρ e s)
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 373/493) (htlo : 3/2 ≤ τ) (hthi : τ ≤ 2) :
    e ≤ energyClauseFourRate σ*τ := by
  have hr := h.rho_le_of_largeValueBound
    (zetaTwelfth_short_largeValueBound (by linarith) htlo)
  obtain ⟨i,hi⟩ := exists_heathBrownNineBranch h.toGeneral.heathBrown_relation
  exact hi.trans (energyClauseFour_zeta_branch hlo hhi htlo hthi hr i)

theorem energyClauseFour_short_zeta {σ τ : ℝ}
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 373/493) (htlo : 1 ≤ τ) (hthi : τ ≤ 2) :
    IsZetaLargeValueEnergyBound σ τ (energyClauseFourRate σ*τ) := by
  by_cases ht : τ < 3/2
  · exact zetaShort_energyBound_any (by linarith) htlo ht _
  · by_contra hnot
    obtain ⟨ρ,e,s,hregion,hlarge⟩ := zetaEnergyRegion_exists_rhoStar_gt_of_not_bound
      (by linarith : 1/2 ≤ σ) (by linarith : σ ≤ 1) (by linarith : 0 ≤ τ) hnot
    exact (not_lt_of_ge (hregion.energyClauseFour hlo hhi (le_of_not_gt ht) hthi)) hlarge

/-- The complete fourth printed clause on its exact closed interval.
No large-values, energy, or moment theorem is accepted as an input. -/
theorem energyClauseFour {σ : ℝ} (hlo : 443/586 ≤ σ) (hhi : σ ≤ 373/493) :
    IsZeroDensityEnergyBound σ (energyClauseFourRate σ/(1-σ)) := by
  apply isZeroDensityEnergyBound_of_bounded_energy_ranges σ (energyClauseFourRate σ) 2
    (by linarith) (by linarith) (energyClauseFourRate_pos hlo hhi).le (by norm_num)
  · intro τ ht
    exact energyClauseFour_short_zeta hlo hhi ht.1 ht.2.le
  · intro τ ht
    exact energyClauseFour_general_bound hlo hhi ht.1 (by linarith [ht.2])

end TaoTrudgianYang2025
