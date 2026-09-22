import TaoTrudgianYang2025.EnergyClauseFourCaps
import TaoTrudgianYang2025.EnergyClauseFourBranches
import TaoTrudgianYang2025.EnergyClauseFourTallCertificates
import TaoTrudgianYang2025.EnergyRegionSupremum

/-!
# General-pattern energy bound for Add-est (iv)

The source region supplies every constraint. Cardinality witnesses at q
and q+1 are distinct from the energy witness at q or q-1.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem energyClauseFour_tall_bound {σ t r : ℝ}
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : 6/5 ≤ t) (hthi : t ≤ 3/2)
    (hg : r ≤ max (18/5-4*σ) (12/5-4*σ+t)) (hcap : r ≤ 3-3*σ) :
    max (r+4-4*σ) ((3-4*σ+5*r)/2) ≤ energyClauseFourRate σ*t := by
  have hC := mul_le_mul_of_nonneg_right (energyClauseFourSecondRate_le σ)
    (by linarith : 0 ≤ t)
  rw [max_eq_right (by linarith : 18/5-4*σ ≤ 12/5-4*σ+t)] at hg
  apply max_le
  · by_cases ht : t ≤ σ+3/5
    · have hc := energyClauseFour_tall_0_0 hlo hhi htlo ht
      linarith
    · have hc := energyClauseFour_tall_0_1 hlo hhi (le_of_not_ge ht) hthi
      linarith
  · by_cases ht : t ≤ σ+3/5
    · have hc := energyClauseFour_tall_1_0 hlo hhi htlo ht
      linarith
    · have hc := energyClauseFour_tall_1_1 hlo hhi (le_of_not_ge ht) hthi
      linarith

theorem InCardinalityEnergyRegion.energyClauseFour_general
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 373/493) (htlo : 2 ≤ τ) (hthi : τ ≤ 4) :
    e ≤ energyClauseFourRate σ*τ := by
  obtain ⟨q,hq,htq,hqt⟩ := energyClauseTwo_power_cover htlo hthi
  have hqNat : 1 ≤ q := by rcases hq with rfl|rfl <;> omega
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  obtain ⟨htone,htthree,hj,hg,hcap⟩ :=
    h.energyClauseFour_cardinality_caps hlo hhi q hq htq hqt
  have hscaled : e/q ≤ energyClauseFourRate σ*(τ/q) := by
    by_cases ht : 6/5 ≤ τ/q
    · exact (h.heathBrown_two_branches_powered q hqNat htthree
        (by linarith)).trans (energyClauseFour_tall_bound hlo hhi ht htthree hg hcap)
    · have htlow : τ/q ≤ 6/5 := le_of_lt (lt_of_not_ge ht)
      rw [max_eq_left (by linarith : 12/5-4*σ+τ/q ≤ 18/5-4*σ)] at hg
      obtain ⟨i,hi⟩ := h.heathBrown_nine_branches_powered q (q-1) hqNat
        (by rcases hq with rfl|rfl <;> omega)
      have halo : (1 : ℝ)/2 ≤ ((q-1 : ℕ) : ℝ)/q := by
        rcases hq with rfl|rfl <;> norm_num
      have hahi : ((q-1 : ℕ) : ℝ)/q ≤ (2 : ℝ)/3 := by
        rcases hq with rfl|rfl <;> norm_num
      by_cases hs : σ ≤ 409/541
      · rw [jutila_twelve_low_sigma hs] at hj
        exact energyClauseFour_low_short_branch hlo hs htone htlow halo hahi
          (by simpa only [add_sub_assoc] using hj) hg i hi
      · have hs' : 409/541 ≤ σ := le_of_not_ge hs
        rw [jutila_twelve_high_sigma hs'] at hj
        exact energyClauseFour_high_short_branch hs' hhi htone htlow halo hahi
          (by simpa only [add_sub_assoc] using hj) hg i hi
  exact (div_le_div_iff_of_pos_right hqpos).1
    (show e/q ≤ (energyClauseFourRate σ*τ)/q by
      simpa only [mul_div_assoc] using hscaled)

theorem energyClauseFour_general_bound {σ τ : ℝ}
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 373/493) (htlo : 2 ≤ τ) (hthi : τ ≤ 4) :
    IsLargeValueEnergyBound σ τ (energyClauseFourRate σ*τ) := by
  by_contra hnot
  obtain ⟨ρ,e,s,hregion,hlarge⟩ := energyRegion_exists_rhoStar_gt_of_not_bound
    (by linarith : 1/2 ≤ σ) (by linarith : σ ≤ 1) (by linarith : 0 ≤ τ) hnot
  exact (not_lt_of_ge ((show InCardinalityEnergyRegion σ τ ρ e from
    ⟨s,hregion⟩).energyClauseFour_general hlo hhi htlo hthi)) hlarge

end TaoTrudgianYang2025
