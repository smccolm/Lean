import TaoTrudgianYang2025.EnergyClauseSevenRates

/-!
# Low-sigma short-height certificates for Add-est (vii)

All nine Heath--Brown branches are checked on the full source interval.
Only the diagonal Jutila cardinality cap is used below the crossover.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem energyClauseSeven_low_0 {σ t : ℝ}
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 97/127)
    (htlo : 1 ≤ t) (hthi : t ≤ 46*σ-34) :
    (0)*t+((4-4*σ)*(2/3)+(1)*(2-2*σ)) ≤ energyClauseSevenFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (46*σ-34) t
    (0) ((4-4*σ)*(2/3)+(1)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSevenFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(42/55))
      (by linarith : 0 ≤ (97/127)-σ)]

theorem energyClauseSeven_low_1 {σ t : ℝ}
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 97/127)
    (htlo : 1 ≤ t) (hthi : t ≤ 46*σ-34) :
    (0)*t+(((3-4*σ)/2)*(1/2)+(5/2)*(2-2*σ)) ≤ energyClauseSevenFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (46*σ-34) t
    (0) (((3-4*σ)/2)*(1/2)+(5/2)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSevenFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(42/55))
      (by linarith : 0 ≤ (97/127)-σ)]

theorem energyClauseSeven_low_2 {σ t : ℝ}
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 97/127)
    (htlo : 1 ≤ t) (hthi : t ≤ 46*σ-34) :
    (2/5)*t+(((12-16*σ)/5)*(1/2)+(8/5)*(2-2*σ)) ≤ energyClauseSevenFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (46*σ-34) t
    (2/5) (((12-16*σ)/5)*(1/2)+(8/5)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSevenFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(42/55))
      (by linarith : 0 ≤ (97/127)-σ)]

theorem energyClauseSeven_low_3 {σ t : ℝ}
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 97/127)
    (htlo : 1 ≤ t) (hthi : t ≤ 46*σ-34) :
    (0)*t+((3-4*σ)*(1/2)+(2)*(2-2*σ)) ≤ energyClauseSevenFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (46*σ-34) t
    (0) ((3-4*σ)*(1/2)+(2)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSevenFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(42/55))
      (by linarith : 0 ≤ (97/127)-σ)]

theorem energyClauseSeven_low_4 {σ t : ℝ}
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 97/127)
    (htlo : 1 ≤ t) (hthi : t ≤ 46*σ-34) :
    (0)*t+((1-2*σ)*(1/2)+(3)*(2-2*σ)) ≤ energyClauseSevenFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (46*σ-34) t
    (0) ((1-2*σ)*(1/2)+(3)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSevenFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(42/55))
      (by linarith : 0 ≤ (97/127)-σ)]

theorem energyClauseSeven_low_5 {σ t : ℝ}
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 97/127)
    (htlo : 1 ≤ t) (hthi : t ≤ 46*σ-34) :
    (2/5)*t+(((8-16*σ)/5)*(1/2)+(12/5)*(2-2*σ)) ≤ energyClauseSevenFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (46*σ-34) t
    (2/5) (((8-16*σ)/5)*(1/2)+(12/5)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSevenFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(42/55))
      (by linarith : 0 ≤ (97/127)-σ)]

theorem energyClauseSeven_low_6 {σ t : ℝ}
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 97/127)
    (htlo : 1 ≤ t) (hthi : t ≤ 46*σ-34) :
    (1/2)*t+((3-4*σ)*(1/2)+(5/4)*(2-2*σ)) ≤ energyClauseSevenFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (46*σ-34) t
    (1/2) ((3-4*σ)*(1/2)+(5/4)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSevenFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(42/55))
      (by linarith : 0 ≤ (97/127)-σ)]

theorem energyClauseSeven_low_7 {σ t : ℝ}
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 97/127)
    (htlo : 1 ≤ t) (hthi : t ≤ 46*σ-34) :
    (1/4)*t+((1-2*σ)*(1/2)+(21/8)*(2-2*σ)) ≤ energyClauseSevenFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (46*σ-34) t
    (1/4) ((1-2*σ)*(1/2)+(21/8)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSevenFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(42/55))
      (by linarith : 0 ≤ (97/127)-σ)]

theorem energyClauseSeven_low_8 {σ t : ℝ}
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 97/127)
    (htlo : 1 ≤ t) (hthi : t ≤ 46*σ-34) :
    (4/5)*t+(((8-16*σ)/5)*(1/2)+(9/5)*(2-2*σ)) ≤ energyClauseSevenFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (46*σ-34) t
    (4/5) (((8-16*σ)/5)*(1/2)+(9/5)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSevenFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(42/55))
      (by linarith : 0 ≤ (97/127)-σ)]

end TaoTrudgianYang2025
