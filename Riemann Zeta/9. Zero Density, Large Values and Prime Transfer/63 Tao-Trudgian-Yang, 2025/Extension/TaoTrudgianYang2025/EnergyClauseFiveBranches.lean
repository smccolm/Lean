import TaoTrudgianYang2025.EnergyClauseFiveLowCertificates
import TaoTrudgianYang2025.EnergyClauseFiveHighCertificates
import TaoTrudgianYang2025.EnergyClauseThreeBranches

/-!
# Nine-branch optimization for Add-est (v)

The high-sigma part ends at the new switch (31σ+2)/22.
Cardinality constraints and the energy-power ratio come from
independent corrected witnesses, not a shared powered point.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem energyClauseFive_low_short_branch {σ t r a e : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 1 ≤ t) (hthi : t ≤ 6/5)
    (halo : 1/2 ≤ a) (hahi : a ≤ 2/3)
    (hj : r ≤ max (2-2*σ) (t+(66-88*σ))) (hg : r ≤ 18/5-4*σ)
    (i : Fin 9) (hb : e ≤ heathBrownNineBranch σ t r a i) :
    e ≤ energyClauseFiveRate σ*t := by
  have hfixed := hb.trans (heathBrownNineBranch_le_extreme_power
    (by linarith) (by linarith) halo hahi i)
  have hA := mul_le_mul_of_nonneg_right (energyClauseFiveFirstRate_le σ)
    (by linarith : 0 ≤ t)
  have hB := mul_le_mul_of_nonneg_right (energyClauseFiveSecondRate_le σ)
    (by linarith : 0 ≤ t)
  fin_cases i
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ 86*σ-64
    · rw [max_eq_left (by linarith : t+(66-88*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseFive_low_0_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 84*σ-312/5
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(66-88*σ))] at hj
        have hc := energyClauseFive_low_0_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseFive_low_0_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ 86*σ-64
    · rw [max_eq_left (by linarith : t+(66-88*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseFive_low_1_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 84*σ-312/5
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(66-88*σ))] at hj
        have hc := energyClauseFive_low_1_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseFive_low_1_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ 86*σ-64
    · rw [max_eq_left (by linarith : t+(66-88*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseFive_low_2_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 84*σ-312/5
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(66-88*σ))] at hj
        have hc := energyClauseFive_low_2_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseFive_low_2_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ 86*σ-64
    · rw [max_eq_left (by linarith : t+(66-88*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseFive_low_3_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 84*σ-312/5
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(66-88*σ))] at hj
        have hc := energyClauseFive_low_3_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseFive_low_3_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ 86*σ-64
    · rw [max_eq_left (by linarith : t+(66-88*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseFive_low_4_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 84*σ-312/5
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(66-88*σ))] at hj
        have hc := energyClauseFive_low_4_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseFive_low_4_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ 86*σ-64
    · rw [max_eq_left (by linarith : t+(66-88*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseFive_low_5_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 84*σ-312/5
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(66-88*σ))] at hj
        have hc := energyClauseFive_low_5_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseFive_low_5_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ 86*σ-64
    · rw [max_eq_left (by linarith : t+(66-88*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseFive_low_6_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 84*σ-312/5
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(66-88*σ))] at hj
        have hc := energyClauseFive_low_6_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseFive_low_6_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ 86*σ-64
    · rw [max_eq_left (by linarith : t+(66-88*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseFive_low_7_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 84*σ-312/5
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(66-88*σ))] at hj
        have hc := energyClauseFive_low_7_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseFive_low_7_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ 86*σ-64
    · rw [max_eq_left (by linarith : t+(66-88*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseFive_low_8_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 84*σ-312/5
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(66-88*σ))] at hj
        have hc := energyClauseFive_low_8_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseFive_low_8_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith

theorem energyClauseFive_high_short_branch {σ t r a e : ℝ}
    (hlo : 171/226 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : 1 ≤ t) (hthi : t ≤ (31*σ+2)/22)
    (halo : 1/2 ≤ a) (hahi : a ≤ 2/3)
    (hj : r ≤ max (2-2*σ) (t+(42/11-(64/11)*σ)))
    (i : Fin 9) (hb : e ≤ heathBrownNineBranch σ t r a i) :
    e ≤ energyClauseFiveRate σ*t := by
  have hfixed := hb.trans (heathBrownNineBranch_le_extreme_power
    (by linarith) (by linarith) halo hahi i)
  have hC := mul_le_mul_of_nonneg_right (energyClauseFiveThirdRate_le σ)
    (by linarith : 0 ≤ t)
  fin_cases i
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht : t ≤ (42*σ-20)/11
    · rw [max_eq_left (by linarith : t+(42/11-(64/11)*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseFive_high_0_0 hlo hhi htlo ht
      linarith
    · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(42/11-(64/11)*σ))] at hj
      have hc := energyClauseFive_high_0_1 hlo hhi (le_of_not_ge ht) hthi
      linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht : t ≤ (42*σ-20)/11
    · rw [max_eq_left (by linarith : t+(42/11-(64/11)*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseFive_high_1_0 hlo hhi htlo ht
      linarith
    · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(42/11-(64/11)*σ))] at hj
      have hc := energyClauseFive_high_1_1 hlo hhi (le_of_not_ge ht) hthi
      linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht : t ≤ (42*σ-20)/11
    · rw [max_eq_left (by linarith : t+(42/11-(64/11)*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseFive_high_2_0 hlo hhi htlo ht
      linarith
    · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(42/11-(64/11)*σ))] at hj
      have hc := energyClauseFive_high_2_1 hlo hhi (le_of_not_ge ht) hthi
      linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht : t ≤ (42*σ-20)/11
    · rw [max_eq_left (by linarith : t+(42/11-(64/11)*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseFive_high_3_0 hlo hhi htlo ht
      linarith
    · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(42/11-(64/11)*σ))] at hj
      have hc := energyClauseFive_high_3_1 hlo hhi (le_of_not_ge ht) hthi
      linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht : t ≤ (42*σ-20)/11
    · rw [max_eq_left (by linarith : t+(42/11-(64/11)*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseFive_high_4_0 hlo hhi htlo ht
      linarith
    · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(42/11-(64/11)*σ))] at hj
      have hc := energyClauseFive_high_4_1 hlo hhi (le_of_not_ge ht) hthi
      linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht : t ≤ (42*σ-20)/11
    · rw [max_eq_left (by linarith : t+(42/11-(64/11)*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseFive_high_5_0 hlo hhi htlo ht
      linarith
    · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(42/11-(64/11)*σ))] at hj
      have hc := energyClauseFive_high_5_1 hlo hhi (le_of_not_ge ht) hthi
      linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht : t ≤ (42*σ-20)/11
    · rw [max_eq_left (by linarith : t+(42/11-(64/11)*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseFive_high_6_0 hlo hhi htlo ht
      linarith
    · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(42/11-(64/11)*σ))] at hj
      have hc := energyClauseFive_high_6_1 hlo hhi (le_of_not_ge ht) hthi
      linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht : t ≤ (42*σ-20)/11
    · rw [max_eq_left (by linarith : t+(42/11-(64/11)*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseFive_high_7_0 hlo hhi htlo ht
      linarith
    · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(42/11-(64/11)*σ))] at hj
      have hc := energyClauseFive_high_7_1 hlo hhi (le_of_not_ge ht) hthi
      linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht : t ≤ (42*σ-20)/11
    · rw [max_eq_left (by linarith : t+(42/11-(64/11)*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseFive_high_8_0 hlo hhi htlo ht
      linarith
    · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(42/11-(64/11)*σ))] at hj
      have hc := energyClauseFive_high_8_1 hlo hhi (le_of_not_ge ht) hthi
      linarith

end TaoTrudgianYang2025
