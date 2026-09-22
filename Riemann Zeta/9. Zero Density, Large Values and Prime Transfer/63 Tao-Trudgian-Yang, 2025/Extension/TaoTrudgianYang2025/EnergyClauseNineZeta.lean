import TaoTrudgianYang2025.EnergyClauseNineRates
import TaoTrudgianYang2025.ZetaTwelfthMoment

/-!
# Full zeta-energy range for Add-est (ix)

Below height 3/2 the actual zeta patterns eventually vanish.
The remaining bounds consume the proved twelfth moment, including
the full source cutoff tau0=8sigma-4.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem energyClauseNine_short_cubic_bound {σ τ : ℝ}
    (hlo : 84/109 ≤ σ) (htlo : 0 ≤ τ) (hthi : τ ≤ 2) :
    3*(2*τ-12*(σ-1/2)) ≤ energyClauseNineRate σ*τ := by
  have hB := mul_le_mul_of_nonneg_right (energyClauseNineRate_ge_short_linear hlo) htlo
  nlinarith [mul_nonneg (by linarith : 0 ≤ 18*σ-9) (by linarith : 0 ≤ 2-τ)]

theorem InZetaLargeValueEnergyRegion.energyClauseNine
    {σ τ ρ e s : ℝ} (h : InZetaLargeValueEnergyRegion σ τ ρ e s)
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 5/6)
    (htlo : 3/2 ≤ τ) (hthi : τ ≤ 8*σ-4) :
    e ≤ energyClauseNineRate σ*τ := by
  by_cases ht : τ ≤ 2
  · have hr := h.rho_le_of_largeValueBound
      (zetaTwelfth_short_largeValueBound (by linarith) htlo)
    exact h.rhoStar_le_three_mul_rho.trans
      ((by linarith : 3*ρ ≤ 3*(2*τ-12*(σ-1/2))).trans
        (energyClauseNine_short_cubic_bound hlo (by linarith) ht))
  · have hr := h.rho_le_of_largeValueBound
      (zetaTwelfth_largeValueBound (by linarith) (by linarith))
    have hb := h.energyClauseOneZeta_of_twelfth_cardinality
      (by linarith) hhi (by linarith) hthi hr
    exact (div_le_iff₀ (by linarith : 0 < τ)).1
      (hb.trans (energyClauseOneZetaRate_le_nine hlo))

theorem energyClauseNine_zeta_bound {σ τ : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 5/6)
    (htlo : 1 ≤ τ) (hthi : τ ≤ 8*σ-4) :
    IsZetaLargeValueEnergyBound σ τ (energyClauseNineRate σ*τ) := by
  by_cases ht : τ < 3/2
  · exact zetaShort_energyBound_any (by linarith) htlo ht _
  · by_contra hnot
    obtain ⟨ρ,e,s,hregion,hlarge⟩ := zetaEnergyRegion_exists_rhoStar_gt_of_not_bound
      (by linarith : 1/2 ≤ σ) (by linarith : σ ≤ 1) (by linarith : 0 ≤ τ) hnot
    exact (not_lt_of_ge (hregion.energyClauseNine hlo hhi (le_of_not_gt ht) hthi)) hlarge

end TaoTrudgianYang2025
