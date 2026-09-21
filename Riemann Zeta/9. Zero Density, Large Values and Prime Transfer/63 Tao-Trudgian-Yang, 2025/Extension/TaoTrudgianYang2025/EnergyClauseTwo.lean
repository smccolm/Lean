import TaoTrudgianYang2025.EnergyClauseTwoGeneral
import TaoTrudgianYang2025.EnergyClauseTwoZetaCertificates
import TaoTrudgianYang2025.ZetaTwelfthLowerShort
import TaoTrudgianYang2025.ZetaBelowTwiceSigma

/-!
# Add-est (ii) from actual general and zeta energy patterns

The short zeta range is supplied explicitly, so the existing endpoint-one
bounded-range transfer suffices. The printed endpoint-two transfer is not
assumed or claimed here.
-/

noncomputable section
namespace TaoTrudgianYang2025

theorem InZetaLargeValueEnergyRegion.energyClauseTwo
    {σ τ ρ e s : ℝ} (h : InZetaLargeValueEnergyRegion σ τ ρ e s)
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4) (htlo : 2*σ ≤ τ) (hthi : τ ≤ 2) :
    e ≤ energyClauseTwoRate σ*τ := by
  have hr := h.rho_le_of_largeValueBound
    (zetaTwelfth_lower_short_largeValueBound hlo (by linarith : 7/5 ≤ τ))
  have hcard : InCardinalityEnergyRegion σ τ ρ e := ⟨s,h.toGeneral⟩
  have hcap := hcard.mean_square_cardinality_powered 2 (by norm_num)
  change ρ/2 ≤ max (2-2*σ) (1-2*σ+τ/2) at hcap
  rw [max_eq_left (by linarith : 1-2*σ+τ/2 ≤ 2-2*σ)] at hcap
  obtain ⟨i,hi⟩ := exists_heathBrownNineBranch h.toGeneral.heathBrown_relation
  exact hi.trans (energyClauseTwo_zeta_branch hlo hhi htlo hthi (by linarith)
    (by linarith) i)

theorem energyClauseTwo_short_zeta {σ τ : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4) (htlo : 1 ≤ τ) (hthi : τ ≤ 2) :
    IsZetaLargeValueEnergyBound σ τ (energyClauseTwoRate σ*τ) := by
  by_cases ht : τ < 2*σ
  · exact zetaBelowTwiceSigma_energyBound_any hlo hhi htlo ht _
  · by_contra hnot
    obtain ⟨ρ,e,s,hregion,hlarge⟩ := zetaEnergyRegion_exists_rhoStar_gt_of_not_bound
      (by linarith : 1/2 ≤ σ) (by linarith : σ ≤ 1) (by linarith : 0 ≤ τ) hnot
    exact (not_lt_of_ge (hregion.energyClauseTwo hlo hhi (le_of_not_gt ht) hthi)) hlarge

/-- The complete second printed clause, with no analytic theorem input. -/
theorem energyClauseTwo {σ : ℝ} (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4) :
    IsZeroDensityEnergyBound σ (energyClauseTwoRate σ/(1-σ)) := by
  apply isZeroDensityEnergyBound_of_bounded_energy_ranges σ (energyClauseTwoRate σ) 2
    (by linarith) (by linarith) (energyClauseTwoRate_pos hlo hhi).le (by norm_num)
  · intro τ ht
    exact energyClauseTwo_short_zeta hlo hhi ht.1 ht.2.le
  · intro τ ht
    exact energyClauseTwo_general_bound hlo hhi ht.1 (by linarith [ht.2])

end TaoTrudgianYang2025
