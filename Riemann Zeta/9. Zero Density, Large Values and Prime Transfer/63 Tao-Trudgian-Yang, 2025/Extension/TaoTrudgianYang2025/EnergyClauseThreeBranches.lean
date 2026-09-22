import TaoTrudgianYang2025.EnergyClauseThreeLowCertificates
import TaoTrudgianYang2025.EnergyClauseThreeHighCertificates
import TaoTrudgianYang2025.HeathBrownNineBranches

/-!
# Exact nine-branch optimization at the independent energy power

The two sigma ranges use their respective Jutila affine terms. Every
branch is checked on each full closed height subinterval.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem heathBrownNineBranch_le_extreme_power {σ t r a : ℝ}
    (hlo : 3/4 ≤ σ) (hhi : σ ≤ 1)
    (halo : 1/2 ≤ a) (hahi : a ≤ 2/3) (i : Fin 9) :
    heathBrownNineBranch σ t r a i ≤
      heathBrownNineBranch σ t r (if i=0 then 2/3 else 1/2) i := by
  have hp₀ := mul_nonneg (by linarith : 0 ≤ 1-σ) (by linarith : 0 ≤ 2/3-a)
  have hp₁ := mul_nonneg (by linarith : 0 ≤ σ-3/4) (by linarith : 0 ≤ a-1/2)
  have hp₂ := mul_nonneg (by linarith : 0 ≤ σ-1/2) (by linarith : 0 ≤ a-1/2)
  fin_cases i <;> norm_num [heathBrownNineBranch] <;> nlinarith

theorem energyClauseThree_low_short_branch {σ t r a e : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 241/319)
    (htlo : 1 ≤ t) (hthi : t ≤ 6/5)
    (halo : 1/2 ≤ a) (hahi : a ≤ 2/3)
    (hj : r ≤ max (2-2*σ) (t+(78-104*σ))) (hg : r ≤ 18/5-4*σ)
    (i : Fin 9) (hb : e ≤ heathBrownNineBranch σ t r a i) :
    e ≤ energyClauseThreeRate σ*t := by
  have hfixed := hb.trans (heathBrownNineBranch_le_extreme_power
    (by linarith) (by linarith) halo hahi i)
  have hA := mul_le_mul_of_nonneg_right (energyClauseThreeFirstRate_le σ)
    (by linarith : 0 ≤ t)
  have hB := mul_le_mul_of_nonneg_right (energyClauseThreeSecondRate_le σ)
    (by linarith : 0 ≤ t)
  have hC := mul_le_mul_of_nonneg_right (energyClauseThreeThirdRate_le σ)
    (by linarith : 0 ≤ t)
  fin_cases i
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ 102*σ-76
    · rw [max_eq_left (by linarith : t+(78-104*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseThree_low_0_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 100*σ-372/5
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(78-104*σ))] at hj
        have hc := energyClauseThree_low_0_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseThree_low_0_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ 102*σ-76
    · rw [max_eq_left (by linarith : t+(78-104*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseThree_low_1_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 100*σ-372/5
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(78-104*σ))] at hj
        have hc := energyClauseThree_low_1_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseThree_low_1_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ 102*σ-76
    · rw [max_eq_left (by linarith : t+(78-104*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseThree_low_2_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 100*σ-372/5
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(78-104*σ))] at hj
        have hc := energyClauseThree_low_2_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseThree_low_2_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ 102*σ-76
    · rw [max_eq_left (by linarith : t+(78-104*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseThree_low_3_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 100*σ-372/5
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(78-104*σ))] at hj
        have hc := energyClauseThree_low_3_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseThree_low_3_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ 102*σ-76
    · rw [max_eq_left (by linarith : t+(78-104*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseThree_low_4_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 100*σ-372/5
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(78-104*σ))] at hj
        have hc := energyClauseThree_low_4_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseThree_low_4_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ 102*σ-76
    · rw [max_eq_left (by linarith : t+(78-104*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseThree_low_5_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 100*σ-372/5
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(78-104*σ))] at hj
        have hc := energyClauseThree_low_5_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseThree_low_5_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ 102*σ-76
    · rw [max_eq_left (by linarith : t+(78-104*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseThree_low_6_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 100*σ-372/5
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(78-104*σ))] at hj
        have hc := energyClauseThree_low_6_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseThree_low_6_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ 102*σ-76
    · rw [max_eq_left (by linarith : t+(78-104*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseThree_low_7_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 100*σ-372/5
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(78-104*σ))] at hj
        have hc := energyClauseThree_low_7_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseThree_low_7_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ 102*σ-76
    · rw [max_eq_left (by linarith : t+(78-104*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseThree_low_8_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 100*σ-372/5
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(78-104*σ))] at hj
        have hc := energyClauseThree_low_8_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseThree_low_8_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith

theorem energyClauseThree_high_short_branch {σ t r a e : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : 1 ≤ t) (hthi : t ≤ 6/5)
    (halo : 1/2 ≤ a) (hahi : a ≤ 2/3)
    (hj : r ≤ max (2-2*σ) (t+(50/13-(76/13)*σ))) (hg : r ≤ 18/5-4*σ)
    (i : Fin 9) (hb : e ≤ heathBrownNineBranch σ t r a i) :
    e ≤ energyClauseThreeRate σ*t := by
  have hfixed := hb.trans (heathBrownNineBranch_le_extreme_power
    (by linarith) (by linarith) halo hahi i)
  have hA := mul_le_mul_of_nonneg_right (energyClauseThreeFirstRate_le σ)
    (by linarith : 0 ≤ t)
  have hB := mul_le_mul_of_nonneg_right (energyClauseThreeSecondRate_le σ)
    (by linarith : 0 ≤ t)
  have hC := mul_le_mul_of_nonneg_right (energyClauseThreeThirdRate_le σ)
    (by linarith : 0 ≤ t)
  fin_cases i
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ (50*σ-24)/13
    · rw [max_eq_left (by linarith : t+(50/13-(76/13)*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseThree_high_0_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 8*(15*σ-2)/65
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(50/13-(76/13)*σ))] at hj
        have hc := energyClauseThree_high_0_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseThree_high_0_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ (50*σ-24)/13
    · rw [max_eq_left (by linarith : t+(50/13-(76/13)*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseThree_high_1_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 8*(15*σ-2)/65
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(50/13-(76/13)*σ))] at hj
        have hc := energyClauseThree_high_1_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseThree_high_1_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ (50*σ-24)/13
    · rw [max_eq_left (by linarith : t+(50/13-(76/13)*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseThree_high_2_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 8*(15*σ-2)/65
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(50/13-(76/13)*σ))] at hj
        have hc := energyClauseThree_high_2_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseThree_high_2_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ (50*σ-24)/13
    · rw [max_eq_left (by linarith : t+(50/13-(76/13)*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseThree_high_3_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 8*(15*σ-2)/65
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(50/13-(76/13)*σ))] at hj
        have hc := energyClauseThree_high_3_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseThree_high_3_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ (50*σ-24)/13
    · rw [max_eq_left (by linarith : t+(50/13-(76/13)*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseThree_high_4_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 8*(15*σ-2)/65
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(50/13-(76/13)*σ))] at hj
        have hc := energyClauseThree_high_4_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseThree_high_4_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ (50*σ-24)/13
    · rw [max_eq_left (by linarith : t+(50/13-(76/13)*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseThree_high_5_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 8*(15*σ-2)/65
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(50/13-(76/13)*σ))] at hj
        have hc := energyClauseThree_high_5_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseThree_high_5_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ (50*σ-24)/13
    · rw [max_eq_left (by linarith : t+(50/13-(76/13)*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseThree_high_6_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 8*(15*σ-2)/65
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(50/13-(76/13)*σ))] at hj
        have hc := energyClauseThree_high_6_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseThree_high_6_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ (50*σ-24)/13
    · rw [max_eq_left (by linarith : t+(50/13-(76/13)*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseThree_high_7_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 8*(15*σ-2)/65
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(50/13-(76/13)*σ))] at hj
        have hc := energyClauseThree_high_7_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseThree_high_7_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ (50*σ-24)/13
    · rw [max_eq_left (by linarith : t+(50/13-(76/13)*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseThree_high_8_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 8*(15*σ-2)/65
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(50/13-(76/13)*σ))] at hj
        have hc := energyClauseThree_high_8_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseThree_high_8_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith

end TaoTrudgianYang2025
