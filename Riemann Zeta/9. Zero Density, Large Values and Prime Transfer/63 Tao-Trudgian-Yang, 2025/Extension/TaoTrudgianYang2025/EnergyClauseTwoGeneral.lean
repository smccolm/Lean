import TaoTrudgianYang2025.EnergyClauseTwoCertificates
import TaoTrudgianYang2025.EnergyClauseTwoCaps
import TaoTrudgianYang2025.EnergyRegionSupremum

/-!
# General-pattern optimization for Add-est (ii)

The two independently powered energy inequalities and three actual cardinality
caps are consumed at linked powers. No fifth-coordinate scaling is asserted.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem energyClauseTwo_primary_high {σ t r : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 6/5 ≤ t) (hthi : t ≤ 3/2)
    (hr : r ≤ max (18/5-4*σ) (12/5-4*σ+t))
    (hcap : r ≤ 3-3*σ) :
    max (r+4-4*σ) ((3-4*σ+5*r)/2) ≤ energyClauseTwoRate σ*t := by
  have hA := mul_le_mul_of_nonneg_right
    (le_max_left (energyClauseTwoFirstRate σ) (energyClauseTwoSecondRate σ))
    (by linarith : 0 ≤ t)
  change energyClauseTwoFirstRate σ*t ≤ energyClauseTwoRate σ*t at hA
  rw [max_eq_right (by linarith : 18/5-4*σ ≤ 12/5-4*σ+t)] at hr
  apply max_le
  · by_cases ht : t ≤ σ+3/5
    · have hc := energyClauseTwo_high_linear_first hlo hhi htlo ht
      linarith
    · have hc := energyClauseTwo_high_constant_first hlo hhi (le_of_not_ge ht) hthi
      linarith
  · by_cases ht : t ≤ σ+3/5
    · have hc := energyClauseTwo_high_linear_second hlo hhi htlo ht
      linarith
    · have hc := energyClauseTwo_high_constant_second hlo hhi (le_of_not_ge ht) hthi
      linarith

theorem energyClauseTwo_primary_low_second {σ t r : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 1 ≤ t) (hthi : t ≤ 6/5)
    (hr : r ≤ 1-2*σ+t) (hg : r ≤ 18/5-4*σ) :
    (3-4*σ+5*r)/2 ≤ energyClauseTwoRate σ*t := by
  have hA := mul_le_mul_of_nonneg_right
    (le_max_left (energyClauseTwoFirstRate σ) (energyClauseTwoSecondRate σ))
    (by linarith : 0 ≤ t)
  change energyClauseTwoFirstRate σ*t ≤ energyClauseTwoRate σ*t at hA
  by_cases ht : t ≤ 13/5-2*σ
  · have hc := energyClauseTwo_low_linear_second hlo hhi htlo ht
    linarith
  · have hc := energyClauseTwo_low_constant_second hlo hhi (le_of_not_ge ht) hthi
    linarith

theorem energyClauseTwo_secondary_bound {σ t r a e : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 1 ≤ t) (hthi : t ≤ 6/5)
    (halo : 1/2 ≤ a) (hahi : a ≤ 2/3)
    (hr : r ≤ 1-2*σ+t) (hg : r ≤ 18/5-4*σ)
    (hprimary : e ≤ 5-6*σ+t) (i : Fin 9)
    (hbranch : e ≤ heathBrownNineBranch σ t r a i) :
    e ≤ energyClauseTwoRate σ*t := by
  have hA := mul_le_mul_of_nonneg_right
    (le_max_left (energyClauseTwoFirstRate σ) (energyClauseTwoSecondRate σ))
    (by linarith : 0 ≤ t)
  have hB := mul_le_mul_of_nonneg_right
    (le_max_right (energyClauseTwoFirstRate σ) (energyClauseTwoSecondRate σ))
    (by linarith : 0 ≤ t)
  change energyClauseTwoFirstRate σ*t ≤ energyClauseTwoRate σ*t at hA
  change energyClauseTwoSecondRate σ*t ≤ energyClauseTwoRate σ*t at hB
  have hp₀ := mul_nonneg (by linarith : 0 ≤ 1-σ) (by linarith : 0 ≤ 2/3-a)
  have hp₁ := mul_nonneg (by linarith : 0 ≤ 3/4-σ) (by linarith : 0 ≤ 2/3-a)
  have hp₂ := mul_nonneg (by linarith : 0 ≤ σ-1/2) (by linarith : 0 ≤ a-1/2)
  fin_cases i
  · norm_num [heathBrownNineBranch] at hbranch
    by_cases ht : t ≤ 13/5-2*σ
    · have hc := energyClauseTwo_secondary_0_low_linear hlo hhi htlo ht
      nlinarith
    · have hc := energyClauseTwo_secondary_0_low_constant hlo hhi (le_of_not_ge ht) hthi
      nlinarith
  · norm_num [heathBrownNineBranch] at hbranch
    by_cases ht : t ≤ 13/5-2*σ
    · have hc := energyClauseTwo_secondary_1_low_linear hlo hhi htlo ht
      nlinarith
    · have hc := energyClauseTwo_secondary_1_low_constant hlo hhi (le_of_not_ge ht) hthi
      nlinarith
  · norm_num [heathBrownNineBranch] at hbranch
    by_cases ht : t ≤ 13/5-2*σ
    · have hc := energyClauseTwo_secondary_2_low_linear hlo hhi htlo ht
      nlinarith
    · have hc := energyClauseTwo_secondary_2_low_constant hlo hhi (le_of_not_ge ht) hthi
      nlinarith
  · norm_num [heathBrownNineBranch] at hbranch
    by_cases ht : t ≤ 13/5-2*σ
    · have hc := energyClauseTwo_secondary_3_low_linear hlo hhi htlo ht
      nlinarith
    · have hc := energyClauseTwo_secondary_3_low_constant hlo hhi (le_of_not_ge ht) hthi
      nlinarith
  · norm_num [heathBrownNineBranch] at hbranch
    by_cases ht : t ≤ σ/2+3/4
    · have hc := energyClauseTwo_trade_three_left hlo hhi htlo ht
      nlinarith
    · have hc := energyClauseTwo_trade_three_right hlo hhi (le_of_not_ge ht) hthi
      linarith
  · norm_num [heathBrownNineBranch] at hbranch
    by_cases ht : t ≤ 13/5-2*σ
    · have hc := energyClauseTwo_secondary_5_low_linear hlo hhi htlo ht
      nlinarith
    · have hc := energyClauseTwo_secondary_5_low_constant hlo hhi (le_of_not_ge ht) hthi
      nlinarith
  · norm_num [heathBrownNineBranch] at hbranch
    by_cases ht : t ≤ 13/5-2*σ
    · have hc := energyClauseTwo_secondary_6_low_linear hlo hhi htlo ht
      nlinarith
    · have hc := energyClauseTwo_secondary_6_low_constant hlo hhi (le_of_not_ge ht) hthi
      nlinarith
  · norm_num [heathBrownNineBranch] at hbranch
    by_cases ht : t ≤ 1+2*σ/15
    · have hc := energyClauseTwo_trade_phase_left hlo hhi htlo ht
      nlinarith
    · have hc := energyClauseTwo_trade_phase_right hlo hhi (le_of_not_ge ht) hthi
      linarith
  · norm_num [heathBrownNineBranch] at hbranch
    by_cases ht : t ≤ 13/5-2*σ
    · by_cases hs : σ ≤ 29/40
      · have hc := energyClauseTwo_secondary_8_low_linear_lower hlo hs htlo ht
        nlinarith
      · have hc := energyClauseTwo_secondary_8_low_linear_upper (le_of_not_ge hs) hhi htlo ht
        nlinarith
    · by_cases hs : σ ≤ 29/40
      · have hc := energyClauseTwo_secondary_8_low_constant_lower hlo hs (le_of_not_ge ht) hthi
        nlinarith
      · have hc := energyClauseTwo_secondary_8_low_constant_upper (le_of_not_ge hs) hhi (le_of_not_ge ht) hthi
        nlinarith

theorem InCardinalityEnergyRegion.energyClauseTwo_general
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4) (htlo : 2 ≤ τ) (hthi : τ ≤ 4) :
    e ≤ energyClauseTwoRate σ*τ := by
  obtain ⟨k,hk,htk,hkt⟩ := energyClauseTwo_power_cover htlo hthi
  have hkNat : 1 ≤ k := by rcases hk with rfl|rfl <;> omega
  have hkpos : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  obtain ⟨htone,htthree,hr,hg,hcap⟩ :=
    h.energyClauseTwo_cardinality_caps (by linarith) k hk htk hkt
  have hprimary := h.heathBrown_two_branches_powered k hkNat htthree (by linarith)
  have hscaled : e/k ≤ energyClauseTwoRate σ*(τ/k) := by
    by_cases ht : 6/5 ≤ τ/k
    · exact hprimary.trans (energyClauseTwo_primary_high hlo hhi ht htthree hg hcap)
    · have htlow : τ/k ≤ 6/5 := le_of_lt (lt_of_not_ge ht)
      rw [max_eq_left (by linarith : 12/5-4*σ+τ/k ≤ 18/5-4*σ)] at hg
      rcases le_max_iff.mp hprimary with hfirst|hsecond
      · obtain ⟨i,hi⟩ := h.heathBrown_nine_branches_powered k (k-1) hkNat
          (by rcases hk with rfl|rfl <;> omega)
        have halo : (1:ℝ)/2 ≤ ((k-1:ℕ):ℝ)/k := by
          rcases hk with rfl|rfl <;> norm_num
        have hahi : ((k-1:ℕ):ℝ)/k ≤ (2:ℝ)/3 := by
          rcases hk with rfl|rfl <;> norm_num
        exact energyClauseTwo_secondary_bound hlo hhi htone htlow halo hahi hr hg
          (by linarith) i hi
      · exact hsecond.trans (energyClauseTwo_primary_low_second hlo hhi htone htlow hr hg)
  have hresult := (div_le_div_iff_of_pos_right hkpos).1
    (show e/k ≤ (energyClauseTwoRate σ*τ)/k by
      simpa only [mul_div_assoc] using hscaled)
  exact hresult

theorem energyClauseTwo_general_bound {σ τ : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4) (htlo : 2 ≤ τ) (hthi : τ ≤ 4) :
    IsLargeValueEnergyBound σ τ (energyClauseTwoRate σ*τ) := by
  by_contra hnot
  obtain ⟨ρ,e,s,hregion,hlarge⟩ := energyRegion_exists_rhoStar_gt_of_not_bound
    (by linarith : 1/2 ≤ σ) (by linarith : σ ≤ 1) (by linarith : 0 ≤ τ) hnot
  exact (not_lt_of_ge ((show InCardinalityEnergyRegion σ τ ρ e from
    ⟨s,hregion⟩).energyClauseTwo_general hlo hhi htlo hthi)) hlarge

end TaoTrudgianYang2025
