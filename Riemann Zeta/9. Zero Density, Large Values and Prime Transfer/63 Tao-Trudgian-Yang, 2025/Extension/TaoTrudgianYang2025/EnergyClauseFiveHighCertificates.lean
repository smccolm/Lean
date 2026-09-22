import TaoTrudgianYang2025.EnergyClauseFiveRates

/-!
# Exact high-sigma short-height certificates for Add-est (v)

The upper height is the new energy-witness switch (31σ+2)/22.
Every branch uses an exact closed-interval rational proof.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem energyClauseFive_high_0_0 {σ t : ℝ}
    (hlo : 171/226 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : 1 ≤ t) (hthi : t ≤ (42*σ-20)/11) :
    ((1)*(0)+(0))*t+((4-4*σ)*(2/3)+(1)*(2-2*σ)) ≤ energyClauseFiveThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((42*σ-20)/11) t
    ((1)*(0)+(0)) ((4-4*σ)*(2/3)+(1)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(171/226))
      (by linarith : 0 ≤ (103/136)-σ)]

theorem energyClauseFive_high_0_1 {σ t : ℝ}
    (hlo : 171/226 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : (42*σ-20)/11 ≤ t) (hthi : t ≤ (31*σ+2)/22) :
    ((1)*(1)+(0))*t+((4-4*σ)*(2/3)+(1)*(42/11-(64/11)*σ)) ≤ energyClauseFiveThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((42*σ-20)/11) ((31*σ+2)/22) t
    ((1)*(1)+(0)) ((4-4*σ)*(2/3)+(1)*(42/11-(64/11)*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(171/226))
      (by linarith : 0 ≤ (103/136)-σ)]

theorem energyClauseFive_high_1_0 {σ t : ℝ}
    (hlo : 171/226 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : 1 ≤ t) (hthi : t ≤ (42*σ-20)/11) :
    ((5/2)*(0)+(0))*t+(((3-4*σ)/2)*(1/2)+(5/2)*(2-2*σ)) ≤ energyClauseFiveThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((42*σ-20)/11) t
    ((5/2)*(0)+(0)) (((3-4*σ)/2)*(1/2)+(5/2)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(171/226))
      (by linarith : 0 ≤ (103/136)-σ)]

theorem energyClauseFive_high_1_1 {σ t : ℝ}
    (hlo : 171/226 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : (42*σ-20)/11 ≤ t) (hthi : t ≤ (31*σ+2)/22) :
    ((5/2)*(1)+(0))*t+(((3-4*σ)/2)*(1/2)+(5/2)*(42/11-(64/11)*σ)) ≤ energyClauseFiveThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((42*σ-20)/11) ((31*σ+2)/22) t
    ((5/2)*(1)+(0)) (((3-4*σ)/2)*(1/2)+(5/2)*(42/11-(64/11)*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(171/226))
      (by linarith : 0 ≤ (103/136)-σ)]

theorem energyClauseFive_high_2_0 {σ t : ℝ}
    (hlo : 171/226 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : 1 ≤ t) (hthi : t ≤ (42*σ-20)/11) :
    ((8/5)*(0)+(2/5))*t+(((12-16*σ)/5)*(1/2)+(8/5)*(2-2*σ)) ≤ energyClauseFiveThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((42*σ-20)/11) t
    ((8/5)*(0)+(2/5)) (((12-16*σ)/5)*(1/2)+(8/5)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(171/226))
      (by linarith : 0 ≤ (103/136)-σ)]

theorem energyClauseFive_high_2_1 {σ t : ℝ}
    (hlo : 171/226 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : (42*σ-20)/11 ≤ t) (hthi : t ≤ (31*σ+2)/22) :
    ((8/5)*(1)+(2/5))*t+(((12-16*σ)/5)*(1/2)+(8/5)*(42/11-(64/11)*σ)) ≤ energyClauseFiveThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((42*σ-20)/11) ((31*σ+2)/22) t
    ((8/5)*(1)+(2/5)) (((12-16*σ)/5)*(1/2)+(8/5)*(42/11-(64/11)*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(171/226))
      (by linarith : 0 ≤ (103/136)-σ)]

theorem energyClauseFive_high_3_0 {σ t : ℝ}
    (hlo : 171/226 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : 1 ≤ t) (hthi : t ≤ (42*σ-20)/11) :
    ((2)*(0)+(0))*t+((3-4*σ)*(1/2)+(2)*(2-2*σ)) ≤ energyClauseFiveThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((42*σ-20)/11) t
    ((2)*(0)+(0)) ((3-4*σ)*(1/2)+(2)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(171/226))
      (by linarith : 0 ≤ (103/136)-σ)]

theorem energyClauseFive_high_3_1 {σ t : ℝ}
    (hlo : 171/226 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : (42*σ-20)/11 ≤ t) (hthi : t ≤ (31*σ+2)/22) :
    ((2)*(1)+(0))*t+((3-4*σ)*(1/2)+(2)*(42/11-(64/11)*σ)) ≤ energyClauseFiveThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((42*σ-20)/11) ((31*σ+2)/22) t
    ((2)*(1)+(0)) ((3-4*σ)*(1/2)+(2)*(42/11-(64/11)*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(171/226))
      (by linarith : 0 ≤ (103/136)-σ)]

theorem energyClauseFive_high_4_0 {σ t : ℝ}
    (hlo : 171/226 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : 1 ≤ t) (hthi : t ≤ (42*σ-20)/11) :
    ((3)*(0)+(0))*t+((1-2*σ)*(1/2)+(3)*(2-2*σ)) ≤ energyClauseFiveThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((42*σ-20)/11) t
    ((3)*(0)+(0)) ((1-2*σ)*(1/2)+(3)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(171/226))
      (by linarith : 0 ≤ (103/136)-σ)]

theorem energyClauseFive_high_4_1 {σ t : ℝ}
    (hlo : 171/226 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : (42*σ-20)/11 ≤ t) (hthi : t ≤ (31*σ+2)/22) :
    ((3)*(1)+(0))*t+((1-2*σ)*(1/2)+(3)*(42/11-(64/11)*σ)) ≤ energyClauseFiveThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((42*σ-20)/11) ((31*σ+2)/22) t
    ((3)*(1)+(0)) ((1-2*σ)*(1/2)+(3)*(42/11-(64/11)*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(171/226))
      (by linarith : 0 ≤ (103/136)-σ)]

theorem energyClauseFive_high_5_0 {σ t : ℝ}
    (hlo : 171/226 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : 1 ≤ t) (hthi : t ≤ (42*σ-20)/11) :
    ((12/5)*(0)+(2/5))*t+(((8-16*σ)/5)*(1/2)+(12/5)*(2-2*σ)) ≤ energyClauseFiveThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((42*σ-20)/11) t
    ((12/5)*(0)+(2/5)) (((8-16*σ)/5)*(1/2)+(12/5)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(171/226))
      (by linarith : 0 ≤ (103/136)-σ)]

theorem energyClauseFive_high_5_1 {σ t : ℝ}
    (hlo : 171/226 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : (42*σ-20)/11 ≤ t) (hthi : t ≤ (31*σ+2)/22) :
    ((12/5)*(1)+(2/5))*t+(((8-16*σ)/5)*(1/2)+(12/5)*(42/11-(64/11)*σ)) ≤ energyClauseFiveThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((42*σ-20)/11) ((31*σ+2)/22) t
    ((12/5)*(1)+(2/5)) (((8-16*σ)/5)*(1/2)+(12/5)*(42/11-(64/11)*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(171/226))
      (by linarith : 0 ≤ (103/136)-σ)]

theorem energyClauseFive_high_6_0 {σ t : ℝ}
    (hlo : 171/226 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : 1 ≤ t) (hthi : t ≤ (42*σ-20)/11) :
    ((5/4)*(0)+(1/2))*t+((3-4*σ)*(1/2)+(5/4)*(2-2*σ)) ≤ energyClauseFiveThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((42*σ-20)/11) t
    ((5/4)*(0)+(1/2)) ((3-4*σ)*(1/2)+(5/4)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(171/226))
      (by linarith : 0 ≤ (103/136)-σ)]

theorem energyClauseFive_high_6_1 {σ t : ℝ}
    (hlo : 171/226 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : (42*σ-20)/11 ≤ t) (hthi : t ≤ (31*σ+2)/22) :
    ((5/4)*(1)+(1/2))*t+((3-4*σ)*(1/2)+(5/4)*(42/11-(64/11)*σ)) ≤ energyClauseFiveThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((42*σ-20)/11) ((31*σ+2)/22) t
    ((5/4)*(1)+(1/2)) ((3-4*σ)*(1/2)+(5/4)*(42/11-(64/11)*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(171/226))
      (by linarith : 0 ≤ (103/136)-σ)]

theorem energyClauseFive_high_7_0 {σ t : ℝ}
    (hlo : 171/226 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : 1 ≤ t) (hthi : t ≤ (42*σ-20)/11) :
    ((21/8)*(0)+(1/4))*t+((1-2*σ)*(1/2)+(21/8)*(2-2*σ)) ≤ energyClauseFiveThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((42*σ-20)/11) t
    ((21/8)*(0)+(1/4)) ((1-2*σ)*(1/2)+(21/8)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(171/226))
      (by linarith : 0 ≤ (103/136)-σ)]

theorem energyClauseFive_high_7_1 {σ t : ℝ}
    (hlo : 171/226 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : (42*σ-20)/11 ≤ t) (hthi : t ≤ (31*σ+2)/22) :
    ((21/8)*(1)+(1/4))*t+((1-2*σ)*(1/2)+(21/8)*(42/11-(64/11)*σ)) ≤ energyClauseFiveThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((42*σ-20)/11) ((31*σ+2)/22) t
    ((21/8)*(1)+(1/4)) ((1-2*σ)*(1/2)+(21/8)*(42/11-(64/11)*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(171/226))
      (by linarith : 0 ≤ (103/136)-σ)]

theorem energyClauseFive_high_8_0 {σ t : ℝ}
    (hlo : 171/226 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : 1 ≤ t) (hthi : t ≤ (42*σ-20)/11) :
    ((9/5)*(0)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(2-2*σ)) ≤ energyClauseFiveThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((42*σ-20)/11) t
    ((9/5)*(0)+(4/5)) (((8-16*σ)/5)*(1/2)+(9/5)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(171/226))
      (by linarith : 0 ≤ (103/136)-σ)]

theorem energyClauseFive_high_8_1 {σ t : ℝ}
    (hlo : 171/226 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : (42*σ-20)/11 ≤ t) (hthi : t ≤ (31*σ+2)/22) :
    ((9/5)*(1)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(42/11-(64/11)*σ)) ≤ energyClauseFiveThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((42*σ-20)/11) ((31*σ+2)/22) t
    ((9/5)*(1)+(4/5)) (((8-16*σ)/5)*(1/2)+(9/5)*(42/11-(64/11)*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(171/226))
      (by linarith : 0 ≤ (103/136)-σ)]

end TaoTrudgianYang2025
