import TaoTrudgianYang2025.EnergyClauseSevenLowCertificates
import TaoTrudgianYang2025.EnergyClauseSevenHighCertificates
import TaoTrudgianYang2025.EnergyClauseThreeBranches

/-!
# Short-height branch consumers for Add-est (vii)

Each sigma range switches at its diagonal-cardinality crossover.
The independent energy power has ratio in [1/2,2/3].
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem energyClauseSeven_low_short_branch {σ t r a e : ℝ}
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 97/127)
    (htlo : 1 ≤ t) (hthi : t ≤ 46*σ-34)
    (halo : 1/2 ≤ a) (hahi : a ≤ 2/3)
    (hj : r ≤ max (2-2*σ) (t+(36-48*σ)))
    (i : Fin 9) (hb : e ≤ heathBrownNineBranch σ t r a i) :
    e ≤ energyClauseSevenRate σ*t := by
  have hfixed := hb.trans (heathBrownNineBranch_le_extreme_power
    (by linarith) (by linarith) halo hahi i)
  have hRate := mul_le_mul_of_nonneg_right (energyClauseSevenFirstRate_le σ)
    (by linarith : 0 ≤ t)
  rw [max_eq_left (by linarith : t+(36-48*σ) ≤ 2-2*σ)] at hj
  fin_cases i
  · norm_num [heathBrownNineBranch] at hfixed
    have hc := energyClauseSeven_low_0 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownNineBranch] at hfixed
    have hc := energyClauseSeven_low_1 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownNineBranch] at hfixed
    have hc := energyClauseSeven_low_2 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownNineBranch] at hfixed
    have hc := energyClauseSeven_low_3 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownNineBranch] at hfixed
    have hc := energyClauseSeven_low_4 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownNineBranch] at hfixed
    have hc := energyClauseSeven_low_5 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownNineBranch] at hfixed
    have hc := energyClauseSeven_low_6 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownNineBranch] at hfixed
    have hc := energyClauseSeven_low_7 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownNineBranch] at hfixed
    have hc := energyClauseSeven_low_8 hlo hhi htlo hthi
    linarith

theorem energyClauseSeven_high_short_branch {σ t r a e : ℝ}
    (hlo : 97/127 ≤ σ) (hhi : σ ≤ 79/103)
    (htlo : 1 ≤ t) (hthi : t ≤ (11*σ-5)/3)
    (halo : 1/2 ≤ a) (hahi : a ≤ 2/3)
    (hj : r ≤ max (2-2*σ) (t+(11/3-(17/3)*σ)))
    (i : Fin 9) (hb : e ≤ heathBrownNineBranch σ t r a i) :
    e ≤ energyClauseSevenRate σ*t := by
  have hfixed := hb.trans (heathBrownNineBranch_le_extreme_power
    (by linarith) (by linarith) halo hahi i)
  have hRate := mul_le_mul_of_nonneg_right (energyClauseSevenSecondRate_le σ)
    (by linarith : 0 ≤ t)
  rw [max_eq_left (by linarith : t+(11/3-(17/3)*σ) ≤ 2-2*σ)] at hj
  fin_cases i
  · norm_num [heathBrownNineBranch] at hfixed
    have hc := energyClauseSeven_high_0 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownNineBranch] at hfixed
    have hc := energyClauseSeven_high_1 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownNineBranch] at hfixed
    have hc := energyClauseSeven_high_2 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownNineBranch] at hfixed
    have hc := energyClauseSeven_high_3 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownNineBranch] at hfixed
    have hc := energyClauseSeven_high_4 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownNineBranch] at hfixed
    have hc := energyClauseSeven_high_5 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownNineBranch] at hfixed
    have hc := energyClauseSeven_high_6 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownNineBranch] at hfixed
    have hc := energyClauseSeven_high_7 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownNineBranch] at hfixed
    have hc := energyClauseSeven_high_8 hlo hhi htlo hthi
    linarith

end TaoTrudgianYang2025
