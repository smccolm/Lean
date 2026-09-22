import TaoTrudgianYang2025.EnergyClauseSixGeneral
import TaoTrudgianYang2025.EnergyClauseSixZetaCertificates
import TaoTrudgianYang2025.ZetaTwelfthMoment

/-!
# Add-est (vi) from corrected powering and the actual zeta moment

The complete short-zeta range is derived explicitly, so the proved
endpoint-one transfer suffices. No endpoint-two corollary is assumed.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem InZetaLargeValueEnergyRegion.energyClauseSix
    {σ τ ρ e s : ℝ} (h : InZetaLargeValueEnergyRegion σ τ ρ e s)
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 31/40) (htlo : 3/2 ≤ τ) (hthi : τ ≤ 2) :
    e ≤ energyClauseSixRate σ*τ := by
  have hr := h.rho_le_of_largeValueBound
    (zetaTwelfth_short_largeValueBound (by linarith) htlo)
  obtain ⟨i,hi⟩ := exists_heathBrownNineBranch h.toGeneral.heathBrown_relation
  exact hi.trans (energyClauseSix_zeta_branch hlo hhi htlo hthi hr i)

theorem energyClauseSix_short_zeta {σ τ : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 31/40) (htlo : 1 ≤ τ) (hthi : τ ≤ 2) :
    IsZetaLargeValueEnergyBound σ τ (energyClauseSixRate σ*τ) := by
  by_cases ht : τ < 3/2
  · exact zetaShort_energyBound_any (by linarith) htlo ht _
  · by_contra hnot
    obtain ⟨ρ,e,s,hregion,hlarge⟩ := zetaEnergyRegion_exists_rhoStar_gt_of_not_bound
      (by linarith : 1/2 ≤ σ) (by linarith : σ ≤ 1) (by linarith : 0 ≤ τ) hnot
    exact (not_lt_of_ge (hregion.energyClauseSix hlo hhi (le_of_not_gt ht) hthi)) hlarge

/-- The complete blueprint bound on its full closed interval.
No large-values, energy, or moment theorem is accepted as an input. -/
theorem energyClauseSix {σ : ℝ} (hlo : 664/877 ≤ σ) (hhi : σ ≤ 31/40) :
    IsZeroDensityEnergyBound σ (energyClauseSixRate σ/(1-σ)) := by
  apply isZeroDensityEnergyBound_of_bounded_energy_ranges σ (energyClauseSixRate σ) 2
    (by linarith) (by linarith) (energyClauseSixRate_pos hlo hhi).le (by norm_num)
  · intro τ ht
    exact energyClauseSix_short_zeta hlo hhi ht.1 ht.2.le
  · intro τ ht
    exact energyClauseSix_general_bound hlo hhi ht.1 (by linarith [ht.2])

/-- Literal source-facing form of blueprint theorem imp-energy-bound4. -/
theorem energyClauseSix_blueprint {σ : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 31/40) :
    zeroDensityEnergyExponent σ ≤
      ((max ((72-91*σ)/(7*(11*σ-8)*(1-σ)))
        (5*(18-19*σ)/(2*(5*σ+3)*(1-σ))) : ℝ) : EReal) := by
  simpa only [energyClauseSixRate_div_eq_blueprint hhi] using
    zeroDensityEnergyExponent_le_of_bound (energyClauseSix hlo hhi)

end TaoTrudgianYang2025
