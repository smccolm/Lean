import TaoTrudgianYang2025.EnergyClauseNineShortCertificates
import TaoTrudgianYang2025.EnergyClauseNineMiddleCertificates
import TaoTrudgianYang2025.EnergyClauseNineTallCertificates
import TaoTrudgianYang2025.EnergyClauseThreeBranches

/-!
# Consumers of the exact Add-est (ix) energy certificates

Cardinality and energy powers are independent. These scalar consumers
are used below on actual corrected-powering region witnesses.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem energyClauseNine_short_branch {σ t r a e : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 4*σ-2 ≤ t) (hthi : t ≤ 6/5)
    (halo : 1/2 ≤ a) (hahi : a ≤ 2/3)
    (hj : r ≤ max (2-2*σ) (t+18/5-(28/5)*σ))
    (i : Fin 9) (hb : e ≤ heathBrownNineBranch σ t r a i) :
    e ≤ energyClauseNineRate σ*t := by
  have hfixed := hb.trans (heathBrownNineBranch_le_extreme_power
    (by linarith) (by linarith) halo hahi i)
  have hRate := mul_le_mul_of_nonneg_right (energyClauseNineSecondRate_le σ)
    (by linarith : 0 ≤ t)
  rcases le_total (t+18/5-(28/5)*σ) (2-2*σ) with hc|hc
  · rw [max_eq_left hc] at hj
    fin_cases i
    · norm_num [heathBrownNineBranch] at hfixed
      have hcert := energyClauseNine_short_diag_0 hlo hhi htlo hthi
      linarith
    · norm_num [heathBrownNineBranch] at hfixed
      have hcert := energyClauseNine_short_diag_1 hlo hhi htlo hthi
      linarith
    · norm_num [heathBrownNineBranch] at hfixed
      have hcert := energyClauseNine_short_diag_2 hlo hhi htlo hthi
      linarith
    · norm_num [heathBrownNineBranch] at hfixed
      have hcert := energyClauseNine_short_diag_3 hlo hhi htlo hthi
      linarith
    · norm_num [heathBrownNineBranch] at hfixed
      have hcert := energyClauseNine_short_diag_4 hlo hhi htlo hthi
      linarith
    · norm_num [heathBrownNineBranch] at hfixed
      have hcert := energyClauseNine_short_diag_5 hlo hhi htlo hthi
      linarith
    · norm_num [heathBrownNineBranch] at hfixed
      have hcert := energyClauseNine_short_diag_6 hlo hhi htlo hthi
      linarith
    · norm_num [heathBrownNineBranch] at hfixed
      have hcert := energyClauseNine_short_diag_7 hlo hhi htlo hthi
      linarith
    · norm_num [heathBrownNineBranch] at hfixed
      have hcert := energyClauseNine_short_diag_8 hlo hhi htlo hthi
      linarith
  · rw [max_eq_right hc] at hj
    fin_cases i
    · norm_num [heathBrownNineBranch] at hfixed
      have hcert := energyClauseNine_short_affine_0 hlo hhi htlo hthi
      linarith
    · norm_num [heathBrownNineBranch] at hfixed
      have hcert := energyClauseNine_short_affine_1 hlo hhi htlo hthi
      linarith
    · norm_num [heathBrownNineBranch] at hfixed
      have hcert := energyClauseNine_short_affine_2 hlo hhi htlo hthi
      linarith
    · norm_num [heathBrownNineBranch] at hfixed
      have hcert := energyClauseNine_short_affine_3 hlo hhi htlo hthi
      linarith
    · norm_num [heathBrownNineBranch] at hfixed
      have hcert := energyClauseNine_short_affine_4 hlo hhi htlo hthi
      linarith
    · norm_num [heathBrownNineBranch] at hfixed
      have hcert := energyClauseNine_short_affine_5 hlo hhi htlo hthi
      linarith
    · norm_num [heathBrownNineBranch] at hfixed
      have hcert := energyClauseNine_short_affine_6 hlo hhi htlo hthi
      linarith
    · norm_num [heathBrownNineBranch] at hfixed
      have hcert := energyClauseNine_short_affine_7 hlo hhi htlo hthi
      linarith
    · norm_num [heathBrownNineBranch] at hfixed
      have hcert := energyClauseNine_short_affine_8 hlo hhi htlo hthi
      linarith

theorem energyClauseNine_middle_first_bound {σ t r : ℝ}
    (hlo : 17/22 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : (13-8*σ)/5 ≤ t) (hthi : t ≤ (4+4*σ)/5) (hr : r ≤ (16-20*σ+t)/3) :
    max (r+4-4*σ) ((3-4*σ+5*r)/2) ≤ energyClauseNineRate σ*t := by
  have hRate := mul_le_mul_of_nonneg_right (energyClauseNineSecondRate_le σ)
    (by linarith : 0 ≤ t)
  apply max_le
  · have hc := energyClauseNine_middle_first_0 hlo htlo hthi
    linarith
  · have hc := energyClauseNine_middle_first_1 hlo htlo hthi
    linarith

theorem energyClauseNine_middle_ninth_bound {σ t r : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 16*σ-11 ≤ t) (hthi : t ≤ (27*σ-18)/2) (hr : r ≤ 9-12*σ+2*t/3) :
    max (r+4-4*σ) ((3-4*σ+5*r)/2) ≤ energyClauseNineRate σ*t := by
  have hRate := mul_le_mul_of_nonneg_right (energyClauseNineFirstRate_le σ)
    (by linarith : 0 ≤ t)
  apply max_le
  · have hc := energyClauseNine_middle_ninth_0 hlo hhi htlo hthi
    linarith
  · have hc := energyClauseNine_middle_ninth_1 hlo hhi htlo hthi
    linarith

theorem energyClauseNine_middle_mixed_bound {σ t r : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : (4+4*σ)/5 ≤ t) (hthi : t ≤ (16*σ-8)/3) (hr : r ≤ 5-7*σ+3*t/4) :
    max (r+4-4*σ) ((3-4*σ+5*r)/2) ≤ energyClauseNineRate σ*t := by
  have hRate := mul_le_mul_of_nonneg_right (energyClauseNineSecondRate_le σ)
    (by linarith : 0 ≤ t)
  apply max_le
  · have hc := energyClauseNine_middle_mixed_0 hlo hhi htlo hthi
    linarith
  · have hc := energyClauseNine_middle_mixed_1 hlo hhi htlo hthi
    linarith

theorem energyClauseNine_cap_bound {σ t r : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5) (htlo : (27*σ-18)/2 ≤ t) (hr : r ≤ 3-3*σ) :
    max (r+4-4*σ) ((3-4*σ+5*r)/2) ≤ energyClauseNineRate σ*t := by
  have hRate := mul_le_mul_of_nonneg_right (energyClauseNineFirstRate_le σ)
    (by linarith : 0 ≤ t)
  apply max_le
  · have hc := energyClauseNine_cap_0 hlo hhi htlo
    linarith
  · have hc := energyClauseNine_cap_1 hlo hhi htlo
    linarith

theorem energyClauseNine_cap_mixed_bound {σ t r : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5) (htlo : (16*σ-8)/3 ≤ t) (hr : r ≤ 3-3*σ) :
    max (r+4-4*σ) ((3-4*σ+5*r)/2) ≤ energyClauseNineRate σ*t := by
  have hRate := mul_le_mul_of_nonneg_right (energyClauseNineSecondRate_le σ)
    (by linarith : 0 ≤ t)
  apply max_le
  · have hc := energyClauseNine_cap_mixed_0 hlo hhi htlo
    linarith
  · have hc := energyClauseNine_cap_mixed_1 hlo hhi htlo
    linarith

theorem energyClauseNine_middle_low_bound {σ t r : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 17/22)
    (htlo : 6/5 ≤ t) (hthi : t ≤ (81-96*σ)/5)
    (hj : r ≤ max (2-2*σ) (t+18/5-(28/5)*σ)) :
    max (r+4-4*σ) ((3-4*σ+5*r)/2) ≤ energyClauseNineRate σ*t := by
  have hRate := mul_le_mul_of_nonneg_right (energyClauseNineFirstRate_le σ)
    (by linarith : 0 ≤ t)
  rcases le_total (t+18/5-(28/5)*σ) (2-2*σ) with hc|hc
  · rw [max_eq_left hc] at hj
    apply max_le
    · have hcert := energyClauseNine_middle_low_diag_0 hlo hhi htlo hthi
      linarith
    · have hcert := energyClauseNine_middle_low_diag_1 hlo hhi htlo hthi
      linarith
  · rw [max_eq_right hc] at hj
    apply max_le
    · have hcert := energyClauseNine_middle_low_affine_0 hlo hhi htlo hthi
      linarith
    · have hcert := energyClauseNine_middle_low_affine_1 hlo hhi htlo hthi
      linarith

theorem energyClauseNine_middle_high_bound {σ t r : ℝ}
    (hlo : 17/22 ≤ σ)
    (htlo : 6/5 ≤ t) (hthi : t ≤ (13-8*σ)/5)
    (hj : r ≤ max (2-2*σ) (t+18/5-(28/5)*σ)) :
    max (r+4-4*σ) ((3-4*σ+5*r)/2) ≤ energyClauseNineRate σ*t := by
  have hRate := mul_le_mul_of_nonneg_right (energyClauseNineSecondRate_le σ)
    (by linarith : 0 ≤ t)
  rcases le_total (t+18/5-(28/5)*σ) (2-2*σ) with hc|hc
  · rw [max_eq_left hc] at hj
    apply max_le
    · have hcert := energyClauseNine_middle_high_diag_0 hlo htlo hthi
      linarith
    · have hcert := energyClauseNine_middle_high_diag_1 hlo htlo hthi
      linarith
  · rw [max_eq_right hc] at hj
    apply max_le
    · have hcert := energyClauseNine_middle_high_affine_0 hlo htlo hthi
      linarith
    · have hcert := energyClauseNine_middle_high_affine_1 hlo htlo hthi
      linarith

theorem energyClauseNine_tall_branch {σ t r : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 6*σ-3) (hr : r ≤ 3-3*σ) (i : Fin 6) :
    heathBrownEnergyBranch σ t r i ≤ energyClauseNineRate σ*t := by
  have hRate := mul_le_mul_of_nonneg_right (energyClauseNineSecondRate_le σ)
    (by linarith : 0 ≤ t)
  fin_cases i
  · norm_num [heathBrownEnergyBranch]
    have hc := energyClauseNine_tall_0 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownEnergyBranch]
    have hc := energyClauseNine_tall_1 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownEnergyBranch]
    have hc := energyClauseNine_tall_2 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownEnergyBranch]
    have hc := energyClauseNine_tall_3 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownEnergyBranch]
    have hc := energyClauseNine_tall_4 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownEnergyBranch]
    have hc := energyClauseNine_tall_5 hlo hhi htlo hthi
    linarith

end TaoTrudgianYang2025
