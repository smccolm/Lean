import TaoTrudgianYang2025.EnergyClauseFourLowCertificates
import TaoTrudgianYang2025.EnergyClauseFourHighCertificates
import TaoTrudgianYang2025.EnergyClauseThreeBranches

/-!
# Nine-branch optimization for Add-est (iv)

The independent energy-power ratio is bounded through the proved
Heath--Brown monotonicity lemma; the cardinality caps are not assumed
to be properties of the same witness.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem energyClauseFour_low_short_branch {σ t r a e : ℝ}
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 409/541)
    (htlo : 1 ≤ t) (hthi : t ≤ 6/5)
    (halo : 1/2 ≤ a) (hahi : a ≤ 2/3)
    (hj : r ≤ max (2-2*σ) (t+(72-96*σ))) (hg : r ≤ 18/5-4*σ)
    (i : Fin 9) (hb : e ≤ heathBrownNineBranch σ t r a i) :
    e ≤ energyClauseFourRate σ*t := by
  have hfixed := hb.trans (heathBrownNineBranch_le_extreme_power
    (by linarith) (by linarith) halo hahi i)
  have hA := mul_le_mul_of_nonneg_right (energyClauseFourFirstRate_le σ)
    (by linarith : 0 ≤ t)
  have hB := mul_le_mul_of_nonneg_right (energyClauseFourSecondRate_le σ)
    (by linarith : 0 ≤ t)
  fin_cases i
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ 94*σ-70
    · rw [max_eq_left (by linarith : t+(72-96*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseFour_low_0_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 92*σ-342/5
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(72-96*σ))] at hj
        have hc := energyClauseFour_low_0_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseFour_low_0_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ 94*σ-70
    · rw [max_eq_left (by linarith : t+(72-96*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseFour_low_1_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 92*σ-342/5
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(72-96*σ))] at hj
        have hc := energyClauseFour_low_1_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseFour_low_1_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ 94*σ-70
    · rw [max_eq_left (by linarith : t+(72-96*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseFour_low_2_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 92*σ-342/5
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(72-96*σ))] at hj
        have hc := energyClauseFour_low_2_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseFour_low_2_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ 94*σ-70
    · rw [max_eq_left (by linarith : t+(72-96*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseFour_low_3_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 92*σ-342/5
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(72-96*σ))] at hj
        have hc := energyClauseFour_low_3_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseFour_low_3_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ 94*σ-70
    · rw [max_eq_left (by linarith : t+(72-96*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseFour_low_4_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 92*σ-342/5
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(72-96*σ))] at hj
        have hc := energyClauseFour_low_4_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseFour_low_4_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ 94*σ-70
    · rw [max_eq_left (by linarith : t+(72-96*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseFour_low_5_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 92*σ-342/5
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(72-96*σ))] at hj
        have hc := energyClauseFour_low_5_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseFour_low_5_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ 94*σ-70
    · rw [max_eq_left (by linarith : t+(72-96*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseFour_low_6_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 92*σ-342/5
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(72-96*σ))] at hj
        have hc := energyClauseFour_low_6_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseFour_low_6_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ 94*σ-70
    · rw [max_eq_left (by linarith : t+(72-96*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseFour_low_7_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 92*σ-342/5
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(72-96*σ))] at hj
        have hc := energyClauseFour_low_7_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseFour_low_7_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ 94*σ-70
    · rw [max_eq_left (by linarith : t+(72-96*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseFour_low_8_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 92*σ-342/5
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(72-96*σ))] at hj
        have hc := energyClauseFour_low_8_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseFour_low_8_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith

theorem energyClauseFour_high_short_branch {σ t r a e : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : 1 ≤ t) (hthi : t ≤ 6/5)
    (halo : 1/2 ≤ a) (hahi : a ≤ 2/3)
    (hj : r ≤ max (2-2*σ) (t+(23/6-(35/6)*σ))) (hg : r ≤ 18/5-4*σ)
    (i : Fin 9) (hb : e ≤ heathBrownNineBranch σ t r a i) :
    e ≤ energyClauseFourRate σ*t := by
  have hfixed := hb.trans (heathBrownNineBranch_le_extreme_power
    (by linarith) (by linarith) halo hahi i)
  have hA := mul_le_mul_of_nonneg_right (energyClauseFourFirstRate_le σ)
    (by linarith : 0 ≤ t)
  have hB := mul_le_mul_of_nonneg_right (energyClauseFourSecondRate_le σ)
    (by linarith : 0 ≤ t)
  fin_cases i
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ (23*σ-11)/6
    · rw [max_eq_left (by linarith : t+(23/6-(35/6)*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseFour_high_0_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 11*σ/6-7/30
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(23/6-(35/6)*σ))] at hj
        have hc := energyClauseFour_high_0_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseFour_high_0_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ (23*σ-11)/6
    · rw [max_eq_left (by linarith : t+(23/6-(35/6)*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseFour_high_1_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 11*σ/6-7/30
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(23/6-(35/6)*σ))] at hj
        have hc := energyClauseFour_high_1_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseFour_high_1_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ (23*σ-11)/6
    · rw [max_eq_left (by linarith : t+(23/6-(35/6)*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseFour_high_2_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 11*σ/6-7/30
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(23/6-(35/6)*σ))] at hj
        have hc := energyClauseFour_high_2_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseFour_high_2_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ (23*σ-11)/6
    · rw [max_eq_left (by linarith : t+(23/6-(35/6)*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseFour_high_3_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 11*σ/6-7/30
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(23/6-(35/6)*σ))] at hj
        have hc := energyClauseFour_high_3_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseFour_high_3_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ (23*σ-11)/6
    · rw [max_eq_left (by linarith : t+(23/6-(35/6)*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseFour_high_4_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 11*σ/6-7/30
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(23/6-(35/6)*σ))] at hj
        have hc := energyClauseFour_high_4_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseFour_high_4_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ (23*σ-11)/6
    · rw [max_eq_left (by linarith : t+(23/6-(35/6)*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseFour_high_5_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 11*σ/6-7/30
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(23/6-(35/6)*σ))] at hj
        have hc := energyClauseFour_high_5_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseFour_high_5_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ (23*σ-11)/6
    · rw [max_eq_left (by linarith : t+(23/6-(35/6)*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseFour_high_6_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 11*σ/6-7/30
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(23/6-(35/6)*σ))] at hj
        have hc := energyClauseFour_high_6_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseFour_high_6_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ (23*σ-11)/6
    · rw [max_eq_left (by linarith : t+(23/6-(35/6)*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseFour_high_7_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 11*σ/6-7/30
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(23/6-(35/6)*σ))] at hj
        have hc := energyClauseFour_high_7_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseFour_high_7_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith
  · norm_num [heathBrownNineBranch] at hfixed
    by_cases ht₁ : t ≤ (23*σ-11)/6
    · rw [max_eq_left (by linarith : t+(23/6-(35/6)*σ) ≤ 2-2*σ)] at hj
      have hc := energyClauseFour_high_8_0 hlo hhi htlo ht₁
      linarith
    · by_cases ht₂ : t ≤ 11*σ/6-7/30
      · rw [max_eq_right (by linarith : 2-2*σ ≤ t+(23/6-(35/6)*σ))] at hj
        have hc := energyClauseFour_high_8_1 hlo hhi (le_of_not_ge ht₁) ht₂
        linarith
      · have hc := energyClauseFour_high_8_2 hlo hhi (le_of_not_ge ht₂) hthi
        linarith

end TaoTrudgianYang2025
