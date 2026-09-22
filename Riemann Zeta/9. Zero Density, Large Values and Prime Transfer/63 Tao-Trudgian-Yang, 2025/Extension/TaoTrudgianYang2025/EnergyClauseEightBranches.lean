import TaoTrudgianYang2025.EnergyClauseEightLowCertificates
import TaoTrudgianYang2025.EnergyClauseEightHighCertificates
import TaoTrudgianYang2025.EnergyClauseThreeBranches

/-!
# Short-height branch consumers for Add-est (viii)

Each sigma range switches at its diagonal-cardinality crossover.
The independent energy power has ratio in [1/2,2/3].
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem energyClauseEight_low_short_branch {σ t r a e : ℝ}
    (hlo : 79/103 ≤ σ) (hhi : σ ≤ 33/43)
    (htlo : 1 ≤ t) (hthi : t ≤ 38*σ-28)
    (halo : 1/2 ≤ a) (hahi : a ≤ 2/3)
    (hj : r ≤ max (2-2*σ) (t+(30-40*σ)))
    (i : Fin 9) (hb : e ≤ heathBrownNineBranch σ t r a i) :
    e ≤ energyClauseEightRate σ*t := by
  have hfixed := hb.trans (heathBrownNineBranch_le_extreme_power
    (by linarith) (by linarith) halo hahi i)
  have hRate := mul_le_mul_of_nonneg_right (energyClauseEightFirstRate_le σ)
    (by linarith : 0 ≤ t)
  rw [max_eq_left (by linarith : t+(30-40*σ) ≤ 2-2*σ)] at hj
  fin_cases i
  · norm_num [heathBrownNineBranch] at hfixed
    have hc := energyClauseEight_low_0 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownNineBranch] at hfixed
    have hc := energyClauseEight_low_1 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownNineBranch] at hfixed
    have hc := energyClauseEight_low_2 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownNineBranch] at hfixed
    have hc := energyClauseEight_low_3 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownNineBranch] at hfixed
    have hc := energyClauseEight_low_4 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownNineBranch] at hfixed
    have hc := energyClauseEight_low_5 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownNineBranch] at hfixed
    have hc := energyClauseEight_low_6 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownNineBranch] at hfixed
    have hc := energyClauseEight_low_7 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownNineBranch] at hfixed
    have hc := energyClauseEight_low_8 hlo hhi htlo hthi
    linarith

theorem energyClauseEight_high_short_branch {σ t r a e : ℝ}
    (hlo : 33/43 ≤ σ) (hhi : σ ≤ 84/109)
    (htlo : 1 ≤ t) (hthi : t ≤ (18*σ-8)/5)
    (halo : 1/2 ≤ a) (hahi : a ≤ 2/3)
    (hj : r ≤ max (2-2*σ) (t+(18/5-(28/5)*σ)))
    (i : Fin 9) (hb : e ≤ heathBrownNineBranch σ t r a i) :
    e ≤ energyClauseEightRate σ*t := by
  have hfixed := hb.trans (heathBrownNineBranch_le_extreme_power
    (by linarith) (by linarith) halo hahi i)
  have hRate := mul_le_mul_of_nonneg_right (energyClauseEightSecondRate_le σ)
    (by linarith : 0 ≤ t)
  rw [max_eq_left (by linarith : t+(18/5-(28/5)*σ) ≤ 2-2*σ)] at hj
  fin_cases i
  · norm_num [heathBrownNineBranch] at hfixed
    have hc := energyClauseEight_high_0 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownNineBranch] at hfixed
    have hc := energyClauseEight_high_1 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownNineBranch] at hfixed
    have hc := energyClauseEight_high_2 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownNineBranch] at hfixed
    have hc := energyClauseEight_high_3 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownNineBranch] at hfixed
    have hc := energyClauseEight_high_4 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownNineBranch] at hfixed
    have hc := energyClauseEight_high_5 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownNineBranch] at hfixed
    have hc := energyClauseEight_high_6 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownNineBranch] at hfixed
    have hc := energyClauseEight_high_7 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownNineBranch] at hfixed
    have hc := energyClauseEight_high_8 hlo hhi htlo hthi
    linarith

end TaoTrudgianYang2025
