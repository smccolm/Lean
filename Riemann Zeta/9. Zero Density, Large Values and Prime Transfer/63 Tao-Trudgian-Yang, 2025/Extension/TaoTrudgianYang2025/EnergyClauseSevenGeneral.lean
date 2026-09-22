import TaoTrudgianYang2025.EnergyClauseSevenCaps
import TaoTrudgianYang2025.EnergyClauseSevenBranches
import TaoTrudgianYang2025.EnergyClauseSevenTallCertificates
import TaoTrudgianYang2025.EnergyRegionSupremum

/-!
# Actual general-pattern bound for Add-est (vii)

The full Jutila theorem supplies cardinality constraints at q and q+1.
Heath--Brown uses the separate energy witness at q or q-1.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem energyClauseSeven_low_tall_bound {σ t r : ℝ}
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 97/127)
    (htlo : 46*σ-34 ≤ t) (hthi : t ≤ 3/2)
    (hj : r ≤ max (2-2*σ) (t+(36-48*σ))) (hcap : r ≤ 3-3*σ) :
    max (r+4-4*σ) ((3-4*σ+5*r)/2) ≤ energyClauseSevenRate σ*t := by
  have hRate := mul_le_mul_of_nonneg_right (energyClauseSevenFirstRate_le σ)
    (by linarith : 0 ≤ t)
  rw [max_eq_right (by linarith : 2-2*σ ≤ t+(36-48*σ))] at hj
  apply max_le
  · by_cases ht : t ≤ 45*σ-33
    · have hc := energyClauseSeven_low_tall_0_0 hlo hhi htlo ht
      linarith
    · have hc := energyClauseSeven_low_tall_0_1 hlo hhi (le_of_not_ge ht) hthi
      linarith
  · by_cases ht : t ≤ 45*σ-33
    · have hc := energyClauseSeven_low_tall_1_0 hlo hhi htlo ht
      linarith
    · have hc := energyClauseSeven_low_tall_1_1 hlo hhi (le_of_not_ge ht) hthi
      linarith

theorem energyClauseSeven_high_tall_bound {σ t r : ℝ}
    (hlo : 97/127 ≤ σ) (hhi : σ ≤ 79/103)
    (htlo : (11*σ-5)/3 ≤ t) (hthi : t ≤ 3/2)
    (hj : r ≤ max (2-2*σ) (t+(11/3-(17/3)*σ))) (hcap : r ≤ 3-3*σ) :
    max (r+4-4*σ) ((3-4*σ+5*r)/2) ≤ energyClauseSevenRate σ*t := by
  have hRate := mul_le_mul_of_nonneg_right (energyClauseSevenSecondRate_le σ)
    (by linarith : 0 ≤ t)
  rw [max_eq_right (by linarith : 2-2*σ ≤ t+(11/3-(17/3)*σ))] at hj
  apply max_le
  · by_cases ht : t ≤ (8*σ-2)/3
    · have hc := energyClauseSeven_high_tall_0_0 hlo hhi htlo ht
      linarith
    · have hc := energyClauseSeven_high_tall_0_1 hlo hhi (le_of_not_ge ht) hthi
      linarith
  · by_cases ht : t ≤ (8*σ-2)/3
    · have hc := energyClauseSeven_high_tall_1_0 hlo hhi htlo ht
      linarith
    · have hc := energyClauseSeven_high_tall_1_1 hlo hhi (le_of_not_ge ht) hthi
      linarith

theorem InCardinalityEnergyRegion.energyClauseSeven_general
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 79/103) (htlo : 2 ≤ τ) (hthi : τ ≤ 4) :
    e ≤ energyClauseSevenRate σ*τ := by
  obtain ⟨q,hq,htq,hqt⟩ := energyClauseTwo_power_cover htlo hthi
  have hqNat : 1 ≤ q := by rcases hq with rfl|rfl <;> omega
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  obtain ⟨htone,htthree,hj,hcap⟩ :=
    h.energyClauseSeven_cardinality_caps hlo hhi q hq htq hqt
  have hscaled : e/q ≤ energyClauseSevenRate σ*(τ/q) := by
    obtain ⟨i,hi⟩ := h.heathBrown_nine_branches_powered q (q-1) hqNat
      (by rcases hq with rfl|rfl <;> omega)
    have halo : (1 : ℝ)/2 ≤ ((q-1 : ℕ) : ℝ)/q := by
      rcases hq with rfl|rfl <;> norm_num
    have hahi : ((q-1 : ℕ) : ℝ)/q ≤ (2 : ℝ)/3 := by
      rcases hq with rfl|rfl <;> norm_num
    by_cases hs : σ ≤ 97/127
    · rw [jutila_six_low_sigma hs] at hj
      by_cases ht : 46*σ-34 ≤ τ/q
      · exact (h.heathBrown_two_branches_powered q hqNat htthree
          (by linarith)).trans (energyClauseSeven_low_tall_bound hlo hs ht htthree
            (by simpa only [add_sub_assoc] using hj) hcap)
      · exact energyClauseSeven_low_short_branch hlo hs htone
          (le_of_lt (lt_of_not_ge ht)) halo hahi
          (by simpa only [add_sub_assoc] using hj) i hi
    · have hs' : 97/127 ≤ σ := le_of_not_ge hs
      rw [jutila_six_high_sigma hs'] at hj
      by_cases ht : (11*σ-5)/3 ≤ τ/q
      · exact (h.heathBrown_two_branches_powered q hqNat htthree
          (by linarith)).trans (energyClauseSeven_high_tall_bound hs' hhi ht htthree
            (by simpa only [add_sub_assoc] using hj) hcap)
      · exact energyClauseSeven_high_short_branch hs' hhi htone
          (le_of_lt (lt_of_not_ge ht)) halo hahi
          (by simpa only [add_sub_assoc] using hj) i hi
  exact (div_le_div_iff_of_pos_right hqpos).1
    (show e/q ≤ (energyClauseSevenRate σ*τ)/q by
      simpa only [mul_div_assoc] using hscaled)

theorem energyClauseSeven_general_bound {σ τ : ℝ}
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 79/103) (htlo : 2 ≤ τ) (hthi : τ ≤ 4) :
    IsLargeValueEnergyBound σ τ (energyClauseSevenRate σ*τ) := by
  by_contra hnot
  obtain ⟨ρ,e,s,hregion,hlarge⟩ := energyRegion_exists_rhoStar_gt_of_not_bound
    (by linarith : 1/2 ≤ σ) (by linarith : σ ≤ 1) (by linarith : 0 ≤ τ) hnot
  exact (not_lt_of_ge ((show InCardinalityEnergyRegion σ τ ρ e from
    ⟨s,hregion⟩).energyClauseSeven_general hlo hhi htlo hthi)) hlarge

end TaoTrudgianYang2025
