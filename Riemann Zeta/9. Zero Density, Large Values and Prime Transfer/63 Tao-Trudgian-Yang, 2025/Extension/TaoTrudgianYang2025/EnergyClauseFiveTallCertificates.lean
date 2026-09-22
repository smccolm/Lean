import TaoTrudgianYang2025.EnergyClauseFiveRates

/-!
# Middle and tall height certificates for Add-est (v)

The q-powered energy witness controls the middle interval beginning
at (31σ+2)/22 and both original tall-height pieces.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem energyClauseFive_middle_0 {σ t : ℝ}
    (hlo : 171/226 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : (31*σ+2)/22 ≤ t) (hthi : t ≤ 6/5) :
    (1)*t+(42/11-(64/11)*σ+4-4*σ) ≤ energyClauseFiveThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((31*σ+2)/22) (6/5) t
    (1) (42/11-(64/11)*σ+4-4*σ) _ htlo hthi
  all_goals
    unfold energyClauseFiveThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(171/226))
      (by linarith : 0 ≤ (103/136)-σ)]

theorem energyClauseFive_middle_1 {σ t : ℝ}
    (hlo : 171/226 ≤ σ) (_hhi : σ ≤ 103/136)
    (htlo : (31*σ+2)/22 ≤ t) (hthi : t ≤ 6/5) :
    (5/2)*t+((3-4*σ+5*(42/11-(64/11)*σ))/2) ≤ energyClauseFiveThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((31*σ+2)/22) (6/5) t
    (5/2) ((3-4*σ+5*(42/11-(64/11)*σ))/2) _ htlo hthi
  all_goals
    unfold energyClauseFiveThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(171/226))
      (by linarith : 0 ≤ (103/136)-σ)]

theorem energyClauseFive_tall_0_0 {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : 6/5 ≤ t) (hthi : t ≤ σ+3/5) :
    (1)*t+((12/5-4*σ)+4-4*σ) ≤ energyClauseFiveThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (6/5) (σ+3/5) t
    (1) ((12/5-4*σ)+4-4*σ) _ htlo hthi
  all_goals
    unfold energyClauseFiveThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(373/493))
      (by linarith : 0 ≤ (103/136)-σ)]

theorem energyClauseFive_tall_0_1 {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : σ+3/5 ≤ t) (hthi : t ≤ 3/2) :
    (0)*t+((3-3*σ)+4-4*σ) ≤ energyClauseFiveThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (σ+3/5) (3/2) t
    (0) ((3-3*σ)+4-4*σ) _ htlo hthi
  all_goals
    unfold energyClauseFiveThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(373/493))
      (by linarith : 0 ≤ (103/136)-σ)]

theorem energyClauseFive_tall_1_0 {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : 6/5 ≤ t) (hthi : t ≤ σ+3/5) :
    ((5/2)*(1))*t+((3-4*σ+5*(12/5-4*σ))/2) ≤ energyClauseFiveThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (6/5) (σ+3/5) t
    ((5/2)*(1)) ((3-4*σ+5*(12/5-4*σ))/2) _ htlo hthi
  all_goals
    unfold energyClauseFiveThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(373/493))
      (by linarith : 0 ≤ (103/136)-σ)]

theorem energyClauseFive_tall_1_1 {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : σ+3/5 ≤ t) (hthi : t ≤ 3/2) :
    ((5/2)*(0))*t+((3-4*σ+5*(3-3*σ))/2) ≤ energyClauseFiveThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (σ+3/5) (3/2) t
    ((5/2)*(0)) ((3-4*σ+5*(3-3*σ))/2) _ htlo hthi
  all_goals
    unfold energyClauseFiveThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(373/493))
      (by linarith : 0 ≤ (103/136)-σ)]

end TaoTrudgianYang2025
