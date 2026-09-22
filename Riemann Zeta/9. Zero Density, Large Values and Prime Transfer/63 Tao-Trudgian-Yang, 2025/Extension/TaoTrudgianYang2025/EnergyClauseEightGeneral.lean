import TaoTrudgianYang2025.EnergyClauseEightCaps
import TaoTrudgianYang2025.EnergyClauseEightBranches
import TaoTrudgianYang2025.EnergyClauseEightTallCertificates
import TaoTrudgianYang2025.EnergyRegionSupremum

/-!
# Actual general-pattern bound for Add-est (viii)

The full Jutila theorem supplies cardinality constraints at q and q+1.
Heath--Brown uses the separate energy witness at q or q-1.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem energyClauseEight_low_tall_bound {σ t r : ℝ}
    (hlo : 79/103 ≤ σ) (hhi : σ ≤ 33/43)
    (htlo : 38*σ-28 ≤ t) (hthi : t ≤ 3/2)
    (hj : r ≤ max (2-2*σ) (t+(30-40*σ))) (hcap : r ≤ 3-3*σ) :
    max (r+4-4*σ) ((3-4*σ+5*r)/2) ≤ energyClauseEightRate σ*t := by
  have hRate := mul_le_mul_of_nonneg_right (energyClauseEightFirstRate_le σ)
    (by linarith : 0 ≤ t)
  rw [max_eq_right (by linarith : 2-2*σ ≤ t+(30-40*σ))] at hj
  apply max_le
  · by_cases ht : t ≤ 37*σ-27
    · have hc := energyClauseEight_low_tall_0_0 hlo hhi htlo ht
      linarith
    · have hc := energyClauseEight_low_tall_0_1 hlo hhi (le_of_not_ge ht) hthi
      linarith
  · by_cases ht : t ≤ 37*σ-27
    · have hc := energyClauseEight_low_tall_1_0 hlo hhi htlo ht
      linarith
    · have hc := energyClauseEight_low_tall_1_1 hlo hhi (le_of_not_ge ht) hthi
      linarith

theorem energyClauseEight_high_tall_bound {σ t r : ℝ}
    (hlo : 33/43 ≤ σ) (hhi : σ ≤ 84/109)
    (htlo : (18*σ-8)/5 ≤ t) (hthi : t ≤ 3/2)
    (hj : r ≤ max (2-2*σ) (t+(18/5-(28/5)*σ))) (hcap : r ≤ 3-3*σ) :
    max (r+4-4*σ) ((3-4*σ+5*r)/2) ≤ energyClauseEightRate σ*t := by
  have hRate := mul_le_mul_of_nonneg_right (energyClauseEightSecondRate_le σ)
    (by linarith : 0 ≤ t)
  rw [max_eq_right (by linarith : 2-2*σ ≤ t+(18/5-(28/5)*σ))] at hj
  apply max_le
  · by_cases ht : t ≤ (13*σ-3)/5
    · have hc := energyClauseEight_high_tall_0_0 hlo hhi htlo ht
      linarith
    · have hc := energyClauseEight_high_tall_0_1 hlo hhi (le_of_not_ge ht) hthi
      linarith
  · by_cases ht : t ≤ (13*σ-3)/5
    · have hc := energyClauseEight_high_tall_1_0 hlo hhi htlo ht
      linarith
    · have hc := energyClauseEight_high_tall_1_1 hlo hhi (le_of_not_ge ht) hthi
      linarith

theorem InCardinalityEnergyRegion.energyClauseEight_general
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (hlo : 79/103 ≤ σ) (hhi : σ ≤ 84/109) (htlo : 2 ≤ τ) (hthi : τ ≤ 4) :
    e ≤ energyClauseEightRate σ*τ := by
  obtain ⟨q,hq,htq,hqt⟩ := energyClauseTwo_power_cover htlo hthi
  have hqNat : 1 ≤ q := by rcases hq with rfl|rfl <;> omega
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  obtain ⟨htone,htthree,hj,hcap⟩ :=
    h.energyClauseEight_cardinality_caps hlo hhi q hq htq hqt
  have hscaled : e/q ≤ energyClauseEightRate σ*(τ/q) := by
    obtain ⟨i,hi⟩ := h.heathBrown_nine_branches_powered q (q-1) hqNat
      (by rcases hq with rfl|rfl <;> omega)
    have halo : (1 : ℝ)/2 ≤ ((q-1 : ℕ) : ℝ)/q := by
      rcases hq with rfl|rfl <;> norm_num
    have hahi : ((q-1 : ℕ) : ℝ)/q ≤ (2 : ℝ)/3 := by
      rcases hq with rfl|rfl <;> norm_num
    by_cases hs : σ ≤ 33/43
    · rw [jutila_five_low_sigma hs] at hj
      by_cases ht : 38*σ-28 ≤ τ/q
      · exact (h.heathBrown_two_branches_powered q hqNat htthree
          (by linarith)).trans (energyClauseEight_low_tall_bound hlo hs ht htthree
            (by simpa only [add_sub_assoc] using hj) hcap)
      · exact energyClauseEight_low_short_branch hlo hs htone
          (le_of_lt (lt_of_not_ge ht)) halo hahi
          (by simpa only [add_sub_assoc] using hj) i hi
    · have hs' : 33/43 ≤ σ := le_of_not_ge hs
      rw [jutila_five_high_sigma hs'] at hj
      by_cases ht : (18*σ-8)/5 ≤ τ/q
      · exact (h.heathBrown_two_branches_powered q hqNat htthree
          (by linarith)).trans (energyClauseEight_high_tall_bound hs' hhi ht htthree
            (by simpa only [add_sub_assoc] using hj) hcap)
      · exact energyClauseEight_high_short_branch hs' hhi htone
          (le_of_lt (lt_of_not_ge ht)) halo hahi
          (by simpa only [add_sub_assoc] using hj) i hi
  exact (div_le_div_iff_of_pos_right hqpos).1
    (show e/q ≤ (energyClauseEightRate σ*τ)/q by
      simpa only [mul_div_assoc] using hscaled)

theorem energyClauseEight_general_bound {σ τ : ℝ}
    (hlo : 79/103 ≤ σ) (hhi : σ ≤ 84/109) (htlo : 2 ≤ τ) (hthi : τ ≤ 4) :
    IsLargeValueEnergyBound σ τ (energyClauseEightRate σ*τ) := by
  by_contra hnot
  obtain ⟨ρ,e,s,hregion,hlarge⟩ := energyRegion_exists_rhoStar_gt_of_not_bound
    (by linarith : 1/2 ≤ σ) (by linarith : σ ≤ 1) (by linarith : 0 ≤ τ) hnot
  exact (not_lt_of_ge ((show InCardinalityEnergyRegion σ τ ρ e from
    ⟨s,hregion⟩).energyClauseEight_general hlo hhi htlo hthi)) hlarge

end TaoTrudgianYang2025
