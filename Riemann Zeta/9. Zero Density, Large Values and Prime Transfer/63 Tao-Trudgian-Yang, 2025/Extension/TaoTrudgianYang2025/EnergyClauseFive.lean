import TaoTrudgianYang2025.EnergyClauseFiveGeneral
import TaoTrudgianYang2025.EnergyClauseFiveZetaCertificates
import TaoTrudgianYang2025.ZetaTwelfthMoment

/-!
# Add-est (v) from corrected powering and the actual zeta moment

The complete short-zeta range is derived explicitly, so the proved
endpoint-one transfer suffices. No endpoint-two corollary is assumed.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem InZetaLargeValueEnergyRegion.energyClauseFive
    {σ τ ρ e s : ℝ} (h : InZetaLargeValueEnergyRegion σ τ ρ e s)
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 103/136) (htlo : 3/2 ≤ τ) (hthi : τ ≤ 2) :
    e ≤ energyClauseFiveRate σ*τ := by
  have hr := h.rho_le_of_largeValueBound
    (zetaTwelfth_short_largeValueBound (by linarith) htlo)
  obtain ⟨i,hi⟩ := exists_heathBrownNineBranch h.toGeneral.heathBrown_relation
  exact hi.trans (energyClauseFive_zeta_branch hlo hhi htlo hthi hr i)

theorem energyClauseFive_short_zeta {σ τ : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 103/136) (htlo : 1 ≤ τ) (hthi : τ ≤ 2) :
    IsZetaLargeValueEnergyBound σ τ (energyClauseFiveRate σ*τ) := by
  by_cases ht : τ < 3/2
  · exact zetaShort_energyBound_any (by linarith) htlo ht _
  · by_contra hnot
    obtain ⟨ρ,e,s,hregion,hlarge⟩ := zetaEnergyRegion_exists_rhoStar_gt_of_not_bound
      (by linarith : 1/2 ≤ σ) (by linarith : σ ≤ 1) (by linarith : 0 ≤ τ) hnot
    exact (not_lt_of_ge (hregion.energyClauseFive hlo hhi (le_of_not_gt ht) hthi)) hlarge

/-- The complete fifth printed clause on its exact closed interval.
No large-values, energy, or moment theorem is accepted as an input. -/
theorem energyClauseFive {σ : ℝ} (hlo : 373/493 ≤ σ) (hhi : σ ≤ 103/136) :
    IsZeroDensityEnergyBound σ (energyClauseFiveRate σ/(1-σ)) := by
  apply isZeroDensityEnergyBound_of_bounded_energy_ranges σ (energyClauseFiveRate σ) 2
    (by linarith) (by linarith) (energyClauseFiveRate_pos hlo hhi).le (by norm_num)
  · intro τ ht
    exact energyClauseFive_short_zeta hlo hhi ht.1 ht.2.le
  · intro τ ht
    exact energyClauseFive_general_bound hlo hhi ht.1 (by linarith [ht.2])

end TaoTrudgianYang2025
