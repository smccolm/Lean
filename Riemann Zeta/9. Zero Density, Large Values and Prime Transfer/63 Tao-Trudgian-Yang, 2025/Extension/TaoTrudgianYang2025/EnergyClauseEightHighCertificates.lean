import TaoTrudgianYang2025.EnergyClauseEightRates

/-!
# High-sigma short-height certificates for Add-est (viii)

All nine Heath--Brown branches are checked on the full source interval.
Only the diagonal Jutila cardinality cap is used below the crossover.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem energyClauseEight_high_0 {σ t : ℝ}
    (hlo : 33/43 ≤ σ) (hhi : σ ≤ 84/109)
    (htlo : 1 ≤ t) (hthi : t ≤ (18*σ-8)/5) :
    (0)*t+((4-4*σ)*(2/3)+(1)*(2-2*σ)) ≤ energyClauseEightSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((18*σ-8)/5) t
    (0) ((4-4*σ)*(2/3)+(1)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseEightSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(33/43))
      (by linarith : 0 ≤ (84/109)-σ)]

theorem energyClauseEight_high_1 {σ t : ℝ}
    (hlo : 33/43 ≤ σ) (hhi : σ ≤ 84/109)
    (htlo : 1 ≤ t) (hthi : t ≤ (18*σ-8)/5) :
    (0)*t+(((3-4*σ)/2)*(1/2)+(5/2)*(2-2*σ)) ≤ energyClauseEightSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((18*σ-8)/5) t
    (0) (((3-4*σ)/2)*(1/2)+(5/2)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseEightSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(33/43))
      (by linarith : 0 ≤ (84/109)-σ)]

theorem energyClauseEight_high_2 {σ t : ℝ}
    (hlo : 33/43 ≤ σ) (hhi : σ ≤ 84/109)
    (htlo : 1 ≤ t) (hthi : t ≤ (18*σ-8)/5) :
    (2/5)*t+(((12-16*σ)/5)*(1/2)+(8/5)*(2-2*σ)) ≤ energyClauseEightSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((18*σ-8)/5) t
    (2/5) (((12-16*σ)/5)*(1/2)+(8/5)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseEightSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(33/43))
      (by linarith : 0 ≤ (84/109)-σ)]

theorem energyClauseEight_high_3 {σ t : ℝ}
    (hlo : 33/43 ≤ σ) (hhi : σ ≤ 84/109)
    (htlo : 1 ≤ t) (hthi : t ≤ (18*σ-8)/5) :
    (0)*t+((3-4*σ)*(1/2)+(2)*(2-2*σ)) ≤ energyClauseEightSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((18*σ-8)/5) t
    (0) ((3-4*σ)*(1/2)+(2)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseEightSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(33/43))
      (by linarith : 0 ≤ (84/109)-σ)]

theorem energyClauseEight_high_4 {σ t : ℝ}
    (hlo : 33/43 ≤ σ) (hhi : σ ≤ 84/109)
    (htlo : 1 ≤ t) (hthi : t ≤ (18*σ-8)/5) :
    (0)*t+((1-2*σ)*(1/2)+(3)*(2-2*σ)) ≤ energyClauseEightSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((18*σ-8)/5) t
    (0) ((1-2*σ)*(1/2)+(3)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseEightSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(33/43))
      (by linarith : 0 ≤ (84/109)-σ)]

theorem energyClauseEight_high_5 {σ t : ℝ}
    (hlo : 33/43 ≤ σ) (hhi : σ ≤ 84/109)
    (htlo : 1 ≤ t) (hthi : t ≤ (18*σ-8)/5) :
    (2/5)*t+(((8-16*σ)/5)*(1/2)+(12/5)*(2-2*σ)) ≤ energyClauseEightSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((18*σ-8)/5) t
    (2/5) (((8-16*σ)/5)*(1/2)+(12/5)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseEightSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(33/43))
      (by linarith : 0 ≤ (84/109)-σ)]

theorem energyClauseEight_high_6 {σ t : ℝ}
    (hlo : 33/43 ≤ σ) (hhi : σ ≤ 84/109)
    (htlo : 1 ≤ t) (hthi : t ≤ (18*σ-8)/5) :
    (1/2)*t+((3-4*σ)*(1/2)+(5/4)*(2-2*σ)) ≤ energyClauseEightSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((18*σ-8)/5) t
    (1/2) ((3-4*σ)*(1/2)+(5/4)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseEightSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(33/43))
      (by linarith : 0 ≤ (84/109)-σ)]

theorem energyClauseEight_high_7 {σ t : ℝ}
    (hlo : 33/43 ≤ σ) (hhi : σ ≤ 84/109)
    (htlo : 1 ≤ t) (hthi : t ≤ (18*σ-8)/5) :
    (1/4)*t+((1-2*σ)*(1/2)+(21/8)*(2-2*σ)) ≤ energyClauseEightSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((18*σ-8)/5) t
    (1/4) ((1-2*σ)*(1/2)+(21/8)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseEightSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(33/43))
      (by linarith : 0 ≤ (84/109)-σ)]

theorem energyClauseEight_high_8 {σ t : ℝ}
    (hlo : 33/43 ≤ σ) (hhi : σ ≤ 84/109)
    (htlo : 1 ≤ t) (hthi : t ≤ (18*σ-8)/5) :
    (4/5)*t+(((8-16*σ)/5)*(1/2)+(9/5)*(2-2*σ)) ≤ energyClauseEightSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((18*σ-8)/5) t
    (4/5) (((8-16*σ)/5)*(1/2)+(9/5)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseEightSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(33/43))
      (by linarith : 0 ≤ (84/109)-σ)]

end TaoTrudgianYang2025
