import TaoTrudgianYang2025.EnergyClauseSevenRates

/-!
# Tall-height certificates for Add-est (vii)

The two simplified Heath--Brown branches meet the two actual Jutila
cardinality caps. Both companion-cap crossover values are retained.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem energyClauseSeven_low_tall_0_0 {σ t : ℝ}
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 97/127)
    (htlo : 46*σ-34 ≤ t) (hthi : t ≤ 45*σ-33) :
    (1)*t+((4-4*σ)+(1)*(36-48*σ)) ≤ energyClauseSevenFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (46*σ-34) (45*σ-33) t
    (1) ((4-4*σ)+(1)*(36-48*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSevenFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(42/55))
      (by linarith : 0 ≤ (97/127)-σ)]

theorem energyClauseSeven_low_tall_0_1 {σ t : ℝ}
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 97/127)
    (htlo : 45*σ-33 ≤ t) (hthi : t ≤ 3/2) :
    (0)*t+((4-4*σ)+(1)*(3-3*σ)) ≤ energyClauseSevenFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (45*σ-33) (3/2) t
    (0) ((4-4*σ)+(1)*(3-3*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSevenFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(42/55))
      (by linarith : 0 ≤ (97/127)-σ)]

theorem energyClauseSeven_low_tall_1_0 {σ t : ℝ}
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 97/127)
    (htlo : 46*σ-34 ≤ t) (hthi : t ≤ 45*σ-33) :
    (5/2)*t+(((3-4*σ)/2)+(5/2)*(36-48*σ)) ≤ energyClauseSevenFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (46*σ-34) (45*σ-33) t
    (5/2) (((3-4*σ)/2)+(5/2)*(36-48*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSevenFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(42/55))
      (by linarith : 0 ≤ (97/127)-σ)]

theorem energyClauseSeven_low_tall_1_1 {σ t : ℝ}
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 97/127)
    (htlo : 45*σ-33 ≤ t) (hthi : t ≤ 3/2) :
    (0)*t+(((3-4*σ)/2)+(5/2)*(3-3*σ)) ≤ energyClauseSevenFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (45*σ-33) (3/2) t
    (0) (((3-4*σ)/2)+(5/2)*(3-3*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSevenFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(42/55))
      (by linarith : 0 ≤ (97/127)-σ)]

theorem energyClauseSeven_high_tall_0_0 {σ t : ℝ}
    (hlo : 97/127 ≤ σ) (hhi : σ ≤ 79/103)
    (htlo : (11*σ-5)/3 ≤ t) (hthi : t ≤ (8*σ-2)/3) :
    (1)*t+((4-4*σ)+(1)*(11/3-(17/3)*σ)) ≤ energyClauseSevenSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((11*σ-5)/3) ((8*σ-2)/3) t
    (1) ((4-4*σ)+(1)*(11/3-(17/3)*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSevenSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(97/127))
      (by linarith : 0 ≤ (79/103)-σ)]

theorem energyClauseSeven_high_tall_0_1 {σ t : ℝ}
    (hlo : 97/127 ≤ σ) (hhi : σ ≤ 79/103)
    (htlo : (8*σ-2)/3 ≤ t) (hthi : t ≤ 3/2) :
    (0)*t+((4-4*σ)+(1)*(3-3*σ)) ≤ energyClauseSevenSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((8*σ-2)/3) (3/2) t
    (0) ((4-4*σ)+(1)*(3-3*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSevenSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(97/127))
      (by linarith : 0 ≤ (79/103)-σ)]

theorem energyClauseSeven_high_tall_1_0 {σ t : ℝ}
    (hlo : 97/127 ≤ σ) (hhi : σ ≤ 79/103)
    (htlo : (11*σ-5)/3 ≤ t) (hthi : t ≤ (8*σ-2)/3) :
    (5/2)*t+(((3-4*σ)/2)+(5/2)*(11/3-(17/3)*σ)) ≤ energyClauseSevenSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((11*σ-5)/3) ((8*σ-2)/3) t
    (5/2) (((3-4*σ)/2)+(5/2)*(11/3-(17/3)*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSevenSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(97/127))
      (by linarith : 0 ≤ (79/103)-σ)]

theorem energyClauseSeven_high_tall_1_1 {σ t : ℝ}
    (hlo : 97/127 ≤ σ) (hhi : σ ≤ 79/103)
    (htlo : (8*σ-2)/3 ≤ t) (hthi : t ≤ 3/2) :
    (0)*t+(((3-4*σ)/2)+(5/2)*(3-3*σ)) ≤ energyClauseSevenSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((8*σ-2)/3) (3/2) t
    (0) (((3-4*σ)/2)+(5/2)*(3-3*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSevenSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(97/127))
      (by linarith : 0 ≤ (79/103)-σ)]

end TaoTrudgianYang2025
