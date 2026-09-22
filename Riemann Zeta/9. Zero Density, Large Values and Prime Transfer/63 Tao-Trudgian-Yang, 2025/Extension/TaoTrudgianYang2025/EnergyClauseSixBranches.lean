import TaoTrudgianYang2025.EnergyClauseSixLowCertificates
import TaoTrudgianYang2025.EnergyClauseSixHighCertificates
import TaoTrudgianYang2025.EnergyClauseThreeBranches

/-!
# Nine-branch short-height bounds for Add-est (vi)

Both sigma ranges have their own exact moving energy-power switch.
All constraints belong to the actual independently powered witnesses.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem energyClauseSix_low_short_branch {σ t r a e : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 281/371)
    (htlo : 1 ≤ t) (hthi : t ≤ 77*σ/2-28)
    (halo : 1/2 ≤ a) (hahi : a ≤ 2/3)
    (hj : r ≤ max (2-2*σ) (t+(60-80*σ)))
    (i : Fin 9) (hb : e ≤ heathBrownNineBranch σ t r a i) :
    e ≤ energyClauseSixRate σ*t := by
  have hfixed := hb.trans (heathBrownNineBranch_le_extreme_power
    (by linarith) (by linarith) halo hahi i)
  have hRate := mul_le_mul_of_nonneg_right (energyClauseSixFirstRate_le σ)
    (by linarith : 0 ≤ t)
  fin_cases i
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht : t ≤ 78*σ-58
    · rw [max_eq_left (by linarith : t+(60-80*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseSix_low_0_0 hlo hhi htlo ht
      linarith
    · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(60-80*σ))] at hj
      have hc := energyClauseSix_low_0_1 hlo hhi (le_of_not_ge ht) hthi
      linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht : t ≤ 78*σ-58
    · rw [max_eq_left (by linarith : t+(60-80*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseSix_low_1_0 hlo hhi htlo ht
      linarith
    · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(60-80*σ))] at hj
      have hc := energyClauseSix_low_1_1 hlo hhi (le_of_not_ge ht) hthi
      linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht : t ≤ 78*σ-58
    · rw [max_eq_left (by linarith : t+(60-80*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseSix_low_2_0 hlo hhi htlo ht
      linarith
    · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(60-80*σ))] at hj
      have hc := energyClauseSix_low_2_1 hlo hhi (le_of_not_ge ht) hthi
      linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht : t ≤ 78*σ-58
    · rw [max_eq_left (by linarith : t+(60-80*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseSix_low_3_0 hlo hhi htlo ht
      linarith
    · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(60-80*σ))] at hj
      have hc := energyClauseSix_low_3_1 hlo hhi (le_of_not_ge ht) hthi
      linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht : t ≤ 78*σ-58
    · rw [max_eq_left (by linarith : t+(60-80*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseSix_low_4_0 hlo hhi htlo ht
      linarith
    · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(60-80*σ))] at hj
      have hc := energyClauseSix_low_4_1 hlo hhi (le_of_not_ge ht) hthi
      linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht : t ≤ 78*σ-58
    · rw [max_eq_left (by linarith : t+(60-80*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseSix_low_5_0 hlo hhi htlo ht
      linarith
    · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(60-80*σ))] at hj
      have hc := energyClauseSix_low_5_1 hlo hhi (le_of_not_ge ht) hthi
      linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht : t ≤ 78*σ-58
    · rw [max_eq_left (by linarith : t+(60-80*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseSix_low_6_0 hlo hhi htlo ht
      linarith
    · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(60-80*σ))] at hj
      have hc := energyClauseSix_low_6_1 hlo hhi (le_of_not_ge ht) hthi
      linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht : t ≤ 78*σ-58
    · rw [max_eq_left (by linarith : t+(60-80*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseSix_low_7_0 hlo hhi htlo ht
      linarith
    · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(60-80*σ))] at hj
      have hc := energyClauseSix_low_7_1 hlo hhi (le_of_not_ge ht) hthi
      linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht : t ≤ 78*σ-58
    · rw [max_eq_left (by linarith : t+(60-80*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseSix_low_8_0 hlo hhi htlo ht
      linarith
    · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(60-80*σ))] at hj
      have hc := energyClauseSix_low_8_1 hlo hhi (le_of_not_ge ht) hthi
      linarith

theorem energyClauseSix_high_short_branch {σ t r a e : ℝ}
    (hlo : 281/371 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : 1 ≤ t) (hthi : t ≤ (14*σ+1)/10)
    (halo : 1/2 ≤ a) (hahi : a ≤ 2/3)
    (hj : r ≤ max (2-2*σ) (t+(19/5-(29/5)*σ)))
    (i : Fin 9) (hb : e ≤ heathBrownNineBranch σ t r a i) :
    e ≤ energyClauseSixRate σ*t := by
  have hfixed := hb.trans (heathBrownNineBranch_le_extreme_power
    (by linarith) (by linarith) halo hahi i)
  have hRate := mul_le_mul_of_nonneg_right (energyClauseSixSecondRate_le σ)
    (by linarith : 0 ≤ t)
  fin_cases i
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht : t ≤ (19*σ-9)/5
    · rw [max_eq_left (by linarith : t+(19/5-(29/5)*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseSix_high_0_0 hlo hhi htlo ht
      linarith
    · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(19/5-(29/5)*σ))] at hj
      have hc := energyClauseSix_high_0_1 hlo hhi (le_of_not_ge ht) hthi
      linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht : t ≤ (19*σ-9)/5
    · rw [max_eq_left (by linarith : t+(19/5-(29/5)*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseSix_high_1_0 hlo hhi htlo ht
      linarith
    · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(19/5-(29/5)*σ))] at hj
      have hc := energyClauseSix_high_1_1 hlo hhi (le_of_not_ge ht) hthi
      linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht : t ≤ (19*σ-9)/5
    · rw [max_eq_left (by linarith : t+(19/5-(29/5)*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseSix_high_2_0 hlo hhi htlo ht
      linarith
    · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(19/5-(29/5)*σ))] at hj
      have hc := energyClauseSix_high_2_1 hlo hhi (le_of_not_ge ht) hthi
      linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht : t ≤ (19*σ-9)/5
    · rw [max_eq_left (by linarith : t+(19/5-(29/5)*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseSix_high_3_0 hlo hhi htlo ht
      linarith
    · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(19/5-(29/5)*σ))] at hj
      have hc := energyClauseSix_high_3_1 hlo hhi (le_of_not_ge ht) hthi
      linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht : t ≤ (19*σ-9)/5
    · rw [max_eq_left (by linarith : t+(19/5-(29/5)*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseSix_high_4_0 hlo hhi htlo ht
      linarith
    · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(19/5-(29/5)*σ))] at hj
      have hc := energyClauseSix_high_4_1 hlo hhi (le_of_not_ge ht) hthi
      linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht : t ≤ (19*σ-9)/5
    · rw [max_eq_left (by linarith : t+(19/5-(29/5)*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseSix_high_5_0 hlo hhi htlo ht
      linarith
    · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(19/5-(29/5)*σ))] at hj
      have hc := energyClauseSix_high_5_1 hlo hhi (le_of_not_ge ht) hthi
      linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht : t ≤ (19*σ-9)/5
    · rw [max_eq_left (by linarith : t+(19/5-(29/5)*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseSix_high_6_0 hlo hhi htlo ht
      linarith
    · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(19/5-(29/5)*σ))] at hj
      have hc := energyClauseSix_high_6_1 hlo hhi (le_of_not_ge ht) hthi
      linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht : t ≤ (19*σ-9)/5
    · rw [max_eq_left (by linarith : t+(19/5-(29/5)*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseSix_high_7_0 hlo hhi htlo ht
      linarith
    · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(19/5-(29/5)*σ))] at hj
      have hc := energyClauseSix_high_7_1 hlo hhi (le_of_not_ge ht) hthi
      linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht : t ≤ (19*σ-9)/5
    · rw [max_eq_left (by linarith : t+(19/5-(29/5)*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseSix_high_8_0 hlo hhi htlo ht
      linarith
    · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(19/5-(29/5)*σ))] at hj
      have hc := energyClauseSix_high_8_1 hlo hhi (le_of_not_ge ht) hthi
      linarith

end TaoTrudgianYang2025
