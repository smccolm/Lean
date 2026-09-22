import TaoTrudgianYang2025.EnergyClauseEightRates
import TaoTrudgianYang2025.HeathBrownNineBranches

/-!
# Short-zeta certificates for Add-est (viii)

The actual twelfth-moment cardinality exponent is substituted into all
nine Heath--Brown branches on the full closed interval [3/2,2].
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem energyClauseEight_zeta_0 {σ t : ℝ}
    (hlo : 79/103 ≤ σ) (hhi : σ ≤ 84/109)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((1)*2+(0))*t+((4-4*σ)+(1)*(6-12*σ)) ≤ energyClauseEightSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (3/2) 2 t
    ((1)*2+(0)) ((4-4*σ)+(1)*(6-12*σ)) _ htlo hthi
  all_goals
    unfold energyClauseEightSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(79/103))
      (by linarith : 0 ≤ (84/109)-σ)]

theorem energyClauseEight_zeta_1 {σ t : ℝ}
    (hlo : 79/103 ≤ σ) (_hhi : σ ≤ 84/109)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((5/2)*2+(0))*t+(((3-4*σ)/2)+(5/2)*(6-12*σ)) ≤ energyClauseEightSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (3/2) 2 t
    ((5/2)*2+(0)) (((3-4*σ)/2)+(5/2)*(6-12*σ)) _ htlo hthi
  all_goals
    unfold energyClauseEightSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(79/103))
      (by linarith : 0 ≤ (84/109)-σ)]

theorem energyClauseEight_zeta_2 {σ t : ℝ}
    (hlo : 79/103 ≤ σ) (_hhi : σ ≤ 84/109)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((8/5)*2+(2/5))*t+(((12-16*σ)/5)+(8/5)*(6-12*σ)) ≤ energyClauseEightSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (3/2) 2 t
    ((8/5)*2+(2/5)) (((12-16*σ)/5)+(8/5)*(6-12*σ)) _ htlo hthi
  all_goals
    unfold energyClauseEightSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(79/103))
      (by linarith : 0 ≤ (84/109)-σ)]

theorem energyClauseEight_zeta_3 {σ t : ℝ}
    (hlo : 79/103 ≤ σ) (_hhi : σ ≤ 84/109)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((2)*2+(0))*t+((3-4*σ)+(2)*(6-12*σ)) ≤ energyClauseEightSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (3/2) 2 t
    ((2)*2+(0)) ((3-4*σ)+(2)*(6-12*σ)) _ htlo hthi
  all_goals
    unfold energyClauseEightSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(79/103))
      (by linarith : 0 ≤ (84/109)-σ)]

theorem energyClauseEight_zeta_4 {σ t : ℝ}
    (hlo : 79/103 ≤ σ) (_hhi : σ ≤ 84/109)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((3)*2+(0))*t+((1-2*σ)+(3)*(6-12*σ)) ≤ energyClauseEightSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (3/2) 2 t
    ((3)*2+(0)) ((1-2*σ)+(3)*(6-12*σ)) _ htlo hthi
  all_goals
    unfold energyClauseEightSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(79/103))
      (by linarith : 0 ≤ (84/109)-σ)]

theorem energyClauseEight_zeta_5 {σ t : ℝ}
    (hlo : 79/103 ≤ σ) (_hhi : σ ≤ 84/109)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((12/5)*2+(2/5))*t+(((8-16*σ)/5)+(12/5)*(6-12*σ)) ≤ energyClauseEightSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (3/2) 2 t
    ((12/5)*2+(2/5)) (((8-16*σ)/5)+(12/5)*(6-12*σ)) _ htlo hthi
  all_goals
    unfold energyClauseEightSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(79/103))
      (by linarith : 0 ≤ (84/109)-σ)]

theorem energyClauseEight_zeta_6 {σ t : ℝ}
    (hlo : 79/103 ≤ σ) (_hhi : σ ≤ 84/109)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((5/4)*2+(1/2))*t+((3-4*σ)+(5/4)*(6-12*σ)) ≤ energyClauseEightSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (3/2) 2 t
    ((5/4)*2+(1/2)) ((3-4*σ)+(5/4)*(6-12*σ)) _ htlo hthi
  all_goals
    unfold energyClauseEightSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(79/103))
      (by linarith : 0 ≤ (84/109)-σ)]

theorem energyClauseEight_zeta_7 {σ t : ℝ}
    (hlo : 79/103 ≤ σ) (_hhi : σ ≤ 84/109)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((21/8)*2+(1/4))*t+((1-2*σ)+(21/8)*(6-12*σ)) ≤ energyClauseEightSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (3/2) 2 t
    ((21/8)*2+(1/4)) ((1-2*σ)+(21/8)*(6-12*σ)) _ htlo hthi
  all_goals
    unfold energyClauseEightSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(79/103))
      (by linarith : 0 ≤ (84/109)-σ)]

theorem energyClauseEight_zeta_8 {σ t : ℝ}
    (hlo : 79/103 ≤ σ) (_hhi : σ ≤ 84/109)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((9/5)*2+(4/5))*t+(((8-16*σ)/5)+(9/5)*(6-12*σ)) ≤ energyClauseEightSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (3/2) 2 t
    ((9/5)*2+(4/5)) (((8-16*σ)/5)+(9/5)*(6-12*σ)) _ htlo hthi
  all_goals
    unfold energyClauseEightSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(79/103))
      (by linarith : 0 ≤ (84/109)-σ)]

theorem energyClauseEight_zeta_branch {σ t r : ℝ}
    (hlo : 79/103 ≤ σ) (hhi : σ ≤ 84/109)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) (hr : r ≤ 2*t-12*(σ-1/2)) (i : Fin 9) :
    heathBrownNineBranch σ t r 1 i ≤ energyClauseEightRate σ*t := by
  have hC := mul_le_mul_of_nonneg_right (energyClauseEightSecondRate_le σ)
    (by linarith : 0 ≤ t)
  fin_cases i
  · norm_num [heathBrownNineBranch]
    have hc := energyClauseEight_zeta_0 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownNineBranch]
    have hc := energyClauseEight_zeta_1 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownNineBranch]
    have hc := energyClauseEight_zeta_2 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownNineBranch]
    have hc := energyClauseEight_zeta_3 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownNineBranch]
    have hc := energyClauseEight_zeta_4 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownNineBranch]
    have hc := energyClauseEight_zeta_5 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownNineBranch]
    have hc := energyClauseEight_zeta_6 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownNineBranch]
    have hc := energyClauseEight_zeta_7 hlo hhi htlo hthi
    linarith
  · norm_num [heathBrownNineBranch]
    have hc := energyClauseEight_zeta_8 hlo hhi htlo hthi
    linarith

end TaoTrudgianYang2025
