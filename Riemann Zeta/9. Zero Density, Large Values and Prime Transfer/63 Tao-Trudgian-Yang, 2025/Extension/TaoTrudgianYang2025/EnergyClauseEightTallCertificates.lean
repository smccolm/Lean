import TaoTrudgianYang2025.EnergyClauseEightRates

/-!
# Tall-height certificates for Add-est (viii)

The two simplified Heath--Brown branches meet the two actual Jutila
cardinality caps. Both companion-cap crossover values are retained.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem energyClauseEight_low_tall_0_0 {σ t : ℝ}
    (hlo : 79/103 ≤ σ) (hhi : σ ≤ 33/43)
    (htlo : 38*σ-28 ≤ t) (hthi : t ≤ 37*σ-27) :
    (1)*t+((4-4*σ)+(1)*(30-40*σ)) ≤ energyClauseEightFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (38*σ-28) (37*σ-27) t
    (1) ((4-4*σ)+(1)*(30-40*σ)) _ htlo hthi
  all_goals
    unfold energyClauseEightFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(79/103))
      (by linarith : 0 ≤ (33/43)-σ)]

theorem energyClauseEight_low_tall_0_1 {σ t : ℝ}
    (hlo : 79/103 ≤ σ) (hhi : σ ≤ 33/43)
    (htlo : 37*σ-27 ≤ t) (hthi : t ≤ 3/2) :
    (0)*t+((4-4*σ)+(1)*(3-3*σ)) ≤ energyClauseEightFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (37*σ-27) (3/2) t
    (0) ((4-4*σ)+(1)*(3-3*σ)) _ htlo hthi
  all_goals
    unfold energyClauseEightFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(79/103))
      (by linarith : 0 ≤ (33/43)-σ)]

theorem energyClauseEight_low_tall_1_0 {σ t : ℝ}
    (hlo : 79/103 ≤ σ) (hhi : σ ≤ 33/43)
    (htlo : 38*σ-28 ≤ t) (hthi : t ≤ 37*σ-27) :
    (5/2)*t+(((3-4*σ)/2)+(5/2)*(30-40*σ)) ≤ energyClauseEightFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (38*σ-28) (37*σ-27) t
    (5/2) (((3-4*σ)/2)+(5/2)*(30-40*σ)) _ htlo hthi
  all_goals
    unfold energyClauseEightFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(79/103))
      (by linarith : 0 ≤ (33/43)-σ)]

theorem energyClauseEight_low_tall_1_1 {σ t : ℝ}
    (hlo : 79/103 ≤ σ) (hhi : σ ≤ 33/43)
    (htlo : 37*σ-27 ≤ t) (hthi : t ≤ 3/2) :
    (0)*t+(((3-4*σ)/2)+(5/2)*(3-3*σ)) ≤ energyClauseEightFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (37*σ-27) (3/2) t
    (0) (((3-4*σ)/2)+(5/2)*(3-3*σ)) _ htlo hthi
  all_goals
    unfold energyClauseEightFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(79/103))
      (by linarith : 0 ≤ (33/43)-σ)]

theorem energyClauseEight_high_tall_0_0 {σ t : ℝ}
    (hlo : 33/43 ≤ σ) (hhi : σ ≤ 84/109)
    (htlo : (18*σ-8)/5 ≤ t) (hthi : t ≤ (13*σ-3)/5) :
    (1)*t+((4-4*σ)+(1)*(18/5-(28/5)*σ)) ≤ energyClauseEightSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((18*σ-8)/5) ((13*σ-3)/5) t
    (1) ((4-4*σ)+(1)*(18/5-(28/5)*σ)) _ htlo hthi
  all_goals
    unfold energyClauseEightSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(33/43))
      (by linarith : 0 ≤ (84/109)-σ)]

theorem energyClauseEight_high_tall_0_1 {σ t : ℝ}
    (hlo : 33/43 ≤ σ) (hhi : σ ≤ 84/109)
    (htlo : (13*σ-3)/5 ≤ t) (hthi : t ≤ 3/2) :
    (0)*t+((4-4*σ)+(1)*(3-3*σ)) ≤ energyClauseEightSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((13*σ-3)/5) (3/2) t
    (0) ((4-4*σ)+(1)*(3-3*σ)) _ htlo hthi
  all_goals
    unfold energyClauseEightSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(33/43))
      (by linarith : 0 ≤ (84/109)-σ)]

theorem energyClauseEight_high_tall_1_0 {σ t : ℝ}
    (hlo : 33/43 ≤ σ) (hhi : σ ≤ 84/109)
    (htlo : (18*σ-8)/5 ≤ t) (hthi : t ≤ (13*σ-3)/5) :
    (5/2)*t+(((3-4*σ)/2)+(5/2)*(18/5-(28/5)*σ)) ≤ energyClauseEightSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((18*σ-8)/5) ((13*σ-3)/5) t
    (5/2) (((3-4*σ)/2)+(5/2)*(18/5-(28/5)*σ)) _ htlo hthi
  all_goals
    unfold energyClauseEightSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(33/43))
      (by linarith : 0 ≤ (84/109)-σ)]

theorem energyClauseEight_high_tall_1_1 {σ t : ℝ}
    (hlo : 33/43 ≤ σ) (hhi : σ ≤ 84/109)
    (htlo : (13*σ-3)/5 ≤ t) (hthi : t ≤ 3/2) :
    (0)*t+(((3-4*σ)/2)+(5/2)*(3-3*σ)) ≤ energyClauseEightSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((13*σ-3)/5) (3/2) t
    (0) (((3-4*σ)/2)+(5/2)*(3-3*σ)) _ htlo hthi
  all_goals
    unfold energyClauseEightSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(33/43))
      (by linarith : 0 ≤ (84/109)-σ)]

end TaoTrudgianYang2025
