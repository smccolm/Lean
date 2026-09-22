import TaoTrudgianYang2025.EnergyClauseFourRates

/-!
# Exact high-sigma short-height certificates for Add-est (iv)

All nine energy branches and all three closed height pieces are
proved by rational algebra. The hypotheses retain the source domain.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem energyClauseFour_high_0_0 {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : 1 ≤ t) (hthi : t ≤ (23*σ-11)/6) :
    ((1)*(0)+(0))*t+((4-4*σ)*(2/3)+(1)*(2-2*σ)) ≤ energyClauseFourSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((23*σ-11)/6) t
    ((1)*(0)+(0)) ((4-4*σ)*(2/3)+(1)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFourSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(409/541))
      (by linarith : 0 ≤ (373/493)-σ)]

theorem energyClauseFour_high_0_1 {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : (23*σ-11)/6 ≤ t) (hthi : t ≤ 11*σ/6-7/30) :
    ((1)*(1)+(0))*t+((4-4*σ)*(2/3)+(1)*(23/6-(35/6)*σ)) ≤ energyClauseFourSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((23*σ-11)/6) (11*σ/6-7/30) t
    ((1)*(1)+(0)) ((4-4*σ)*(2/3)+(1)*(23/6-(35/6)*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFourSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(409/541))
      (by linarith : 0 ≤ (373/493)-σ)]

theorem energyClauseFour_high_0_2 {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : 11*σ/6-7/30 ≤ t) (hthi : t ≤ 6/5) :
    ((1)*(0)+(0))*t+((4-4*σ)*(2/3)+(1)*(18/5-4*σ)) ≤ energyClauseFourSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (11*σ/6-7/30) (6/5) t
    ((1)*(0)+(0)) ((4-4*σ)*(2/3)+(1)*(18/5-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFourSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(409/541))
      (by linarith : 0 ≤ (373/493)-σ)]

theorem energyClauseFour_high_1_0 {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : 1 ≤ t) (hthi : t ≤ (23*σ-11)/6) :
    ((5/2)*(0)+(0))*t+(((3-4*σ)/2)*(1/2)+(5/2)*(2-2*σ)) ≤ energyClauseFourSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((23*σ-11)/6) t
    ((5/2)*(0)+(0)) (((3-4*σ)/2)*(1/2)+(5/2)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFourSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(409/541))
      (by linarith : 0 ≤ (373/493)-σ)]

theorem energyClauseFour_high_1_1 {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : (23*σ-11)/6 ≤ t) (hthi : t ≤ 11*σ/6-7/30) :
    ((5/2)*(1)+(0))*t+(((3-4*σ)/2)*(1/2)+(5/2)*(23/6-(35/6)*σ)) ≤ energyClauseFourSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((23*σ-11)/6) (11*σ/6-7/30) t
    ((5/2)*(1)+(0)) (((3-4*σ)/2)*(1/2)+(5/2)*(23/6-(35/6)*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFourSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(409/541))
      (by linarith : 0 ≤ (373/493)-σ)]

theorem energyClauseFour_high_1_2 {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (_hhi : σ ≤ 373/493)
    (htlo : 11*σ/6-7/30 ≤ t) (hthi : t ≤ 6/5) :
    ((5/2)*(0)+(0))*t+(((3-4*σ)/2)*(1/2)+(5/2)*(18/5-4*σ)) ≤ energyClauseFourSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (11*σ/6-7/30) (6/5) t
    ((5/2)*(0)+(0)) (((3-4*σ)/2)*(1/2)+(5/2)*(18/5-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFourSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(409/541))
      (by linarith : 0 ≤ (373/493)-σ)]

theorem energyClauseFour_high_2_0 {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : 1 ≤ t) (hthi : t ≤ (23*σ-11)/6) :
    ((8/5)*(0)+(2/5))*t+(((12-16*σ)/5)*(1/2)+(8/5)*(2-2*σ)) ≤ energyClauseFourSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((23*σ-11)/6) t
    ((8/5)*(0)+(2/5)) (((12-16*σ)/5)*(1/2)+(8/5)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFourSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(409/541))
      (by linarith : 0 ≤ (373/493)-σ)]

theorem energyClauseFour_high_2_1 {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : (23*σ-11)/6 ≤ t) (hthi : t ≤ 11*σ/6-7/30) :
    ((8/5)*(1)+(2/5))*t+(((12-16*σ)/5)*(1/2)+(8/5)*(23/6-(35/6)*σ)) ≤ energyClauseFourSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((23*σ-11)/6) (11*σ/6-7/30) t
    ((8/5)*(1)+(2/5)) (((12-16*σ)/5)*(1/2)+(8/5)*(23/6-(35/6)*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFourSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(409/541))
      (by linarith : 0 ≤ (373/493)-σ)]

theorem energyClauseFour_high_2_2 {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : 11*σ/6-7/30 ≤ t) (hthi : t ≤ 6/5) :
    ((8/5)*(0)+(2/5))*t+(((12-16*σ)/5)*(1/2)+(8/5)*(18/5-4*σ)) ≤ energyClauseFourSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (11*σ/6-7/30) (6/5) t
    ((8/5)*(0)+(2/5)) (((12-16*σ)/5)*(1/2)+(8/5)*(18/5-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFourSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(409/541))
      (by linarith : 0 ≤ (373/493)-σ)]

theorem energyClauseFour_high_3_0 {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : 1 ≤ t) (hthi : t ≤ (23*σ-11)/6) :
    ((2)*(0)+(0))*t+((3-4*σ)*(1/2)+(2)*(2-2*σ)) ≤ energyClauseFourSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((23*σ-11)/6) t
    ((2)*(0)+(0)) ((3-4*σ)*(1/2)+(2)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFourSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(409/541))
      (by linarith : 0 ≤ (373/493)-σ)]

theorem energyClauseFour_high_3_1 {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : (23*σ-11)/6 ≤ t) (hthi : t ≤ 11*σ/6-7/30) :
    ((2)*(1)+(0))*t+((3-4*σ)*(1/2)+(2)*(23/6-(35/6)*σ)) ≤ energyClauseFourSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((23*σ-11)/6) (11*σ/6-7/30) t
    ((2)*(1)+(0)) ((3-4*σ)*(1/2)+(2)*(23/6-(35/6)*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFourSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(409/541))
      (by linarith : 0 ≤ (373/493)-σ)]

theorem energyClauseFour_high_3_2 {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (_hhi : σ ≤ 373/493)
    (htlo : 11*σ/6-7/30 ≤ t) (hthi : t ≤ 6/5) :
    ((2)*(0)+(0))*t+((3-4*σ)*(1/2)+(2)*(18/5-4*σ)) ≤ energyClauseFourSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (11*σ/6-7/30) (6/5) t
    ((2)*(0)+(0)) ((3-4*σ)*(1/2)+(2)*(18/5-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFourSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(409/541))
      (by linarith : 0 ≤ (373/493)-σ)]

theorem energyClauseFour_high_4_0 {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : 1 ≤ t) (hthi : t ≤ (23*σ-11)/6) :
    ((3)*(0)+(0))*t+((1-2*σ)*(1/2)+(3)*(2-2*σ)) ≤ energyClauseFourSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((23*σ-11)/6) t
    ((3)*(0)+(0)) ((1-2*σ)*(1/2)+(3)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFourSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(409/541))
      (by linarith : 0 ≤ (373/493)-σ)]

theorem energyClauseFour_high_4_1 {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : (23*σ-11)/6 ≤ t) (hthi : t ≤ 11*σ/6-7/30) :
    ((3)*(1)+(0))*t+((1-2*σ)*(1/2)+(3)*(23/6-(35/6)*σ)) ≤ energyClauseFourSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((23*σ-11)/6) (11*σ/6-7/30) t
    ((3)*(1)+(0)) ((1-2*σ)*(1/2)+(3)*(23/6-(35/6)*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFourSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(409/541))
      (by linarith : 0 ≤ (373/493)-σ)]

theorem energyClauseFour_high_4_2 {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (_hhi : σ ≤ 373/493)
    (htlo : 11*σ/6-7/30 ≤ t) (hthi : t ≤ 6/5) :
    ((3)*(0)+(0))*t+((1-2*σ)*(1/2)+(3)*(18/5-4*σ)) ≤ energyClauseFourSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (11*σ/6-7/30) (6/5) t
    ((3)*(0)+(0)) ((1-2*σ)*(1/2)+(3)*(18/5-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFourSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(409/541))
      (by linarith : 0 ≤ (373/493)-σ)]

theorem energyClauseFour_high_5_0 {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : 1 ≤ t) (hthi : t ≤ (23*σ-11)/6) :
    ((12/5)*(0)+(2/5))*t+(((8-16*σ)/5)*(1/2)+(12/5)*(2-2*σ)) ≤ energyClauseFourSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((23*σ-11)/6) t
    ((12/5)*(0)+(2/5)) (((8-16*σ)/5)*(1/2)+(12/5)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFourSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(409/541))
      (by linarith : 0 ≤ (373/493)-σ)]

theorem energyClauseFour_high_5_1 {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : (23*σ-11)/6 ≤ t) (hthi : t ≤ 11*σ/6-7/30) :
    ((12/5)*(1)+(2/5))*t+(((8-16*σ)/5)*(1/2)+(12/5)*(23/6-(35/6)*σ)) ≤ energyClauseFourSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((23*σ-11)/6) (11*σ/6-7/30) t
    ((12/5)*(1)+(2/5)) (((8-16*σ)/5)*(1/2)+(12/5)*(23/6-(35/6)*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFourSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(409/541))
      (by linarith : 0 ≤ (373/493)-σ)]

theorem energyClauseFour_high_5_2 {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (_hhi : σ ≤ 373/493)
    (htlo : 11*σ/6-7/30 ≤ t) (hthi : t ≤ 6/5) :
    ((12/5)*(0)+(2/5))*t+(((8-16*σ)/5)*(1/2)+(12/5)*(18/5-4*σ)) ≤ energyClauseFourSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (11*σ/6-7/30) (6/5) t
    ((12/5)*(0)+(2/5)) (((8-16*σ)/5)*(1/2)+(12/5)*(18/5-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFourSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(409/541))
      (by linarith : 0 ≤ (373/493)-σ)]

theorem energyClauseFour_high_6_0 {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : 1 ≤ t) (hthi : t ≤ (23*σ-11)/6) :
    ((5/4)*(0)+(1/2))*t+((3-4*σ)*(1/2)+(5/4)*(2-2*σ)) ≤ energyClauseFourSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((23*σ-11)/6) t
    ((5/4)*(0)+(1/2)) ((3-4*σ)*(1/2)+(5/4)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFourSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(409/541))
      (by linarith : 0 ≤ (373/493)-σ)]

theorem energyClauseFour_high_6_1 {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : (23*σ-11)/6 ≤ t) (hthi : t ≤ 11*σ/6-7/30) :
    ((5/4)*(1)+(1/2))*t+((3-4*σ)*(1/2)+(5/4)*(23/6-(35/6)*σ)) ≤ energyClauseFourSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((23*σ-11)/6) (11*σ/6-7/30) t
    ((5/4)*(1)+(1/2)) ((3-4*σ)*(1/2)+(5/4)*(23/6-(35/6)*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFourSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(409/541))
      (by linarith : 0 ≤ (373/493)-σ)]

theorem energyClauseFour_high_6_2 {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : 11*σ/6-7/30 ≤ t) (hthi : t ≤ 6/5) :
    ((5/4)*(0)+(1/2))*t+((3-4*σ)*(1/2)+(5/4)*(18/5-4*σ)) ≤ energyClauseFourSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (11*σ/6-7/30) (6/5) t
    ((5/4)*(0)+(1/2)) ((3-4*σ)*(1/2)+(5/4)*(18/5-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFourSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(409/541))
      (by linarith : 0 ≤ (373/493)-σ)]

theorem energyClauseFour_high_7_0 {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : 1 ≤ t) (hthi : t ≤ (23*σ-11)/6) :
    ((21/8)*(0)+(1/4))*t+((1-2*σ)*(1/2)+(21/8)*(2-2*σ)) ≤ energyClauseFourSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((23*σ-11)/6) t
    ((21/8)*(0)+(1/4)) ((1-2*σ)*(1/2)+(21/8)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFourSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(409/541))
      (by linarith : 0 ≤ (373/493)-σ)]

theorem energyClauseFour_high_7_1 {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : (23*σ-11)/6 ≤ t) (hthi : t ≤ 11*σ/6-7/30) :
    ((21/8)*(1)+(1/4))*t+((1-2*σ)*(1/2)+(21/8)*(23/6-(35/6)*σ)) ≤ energyClauseFourSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((23*σ-11)/6) (11*σ/6-7/30) t
    ((21/8)*(1)+(1/4)) ((1-2*σ)*(1/2)+(21/8)*(23/6-(35/6)*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFourSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(409/541))
      (by linarith : 0 ≤ (373/493)-σ)]

theorem energyClauseFour_high_7_2 {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (_hhi : σ ≤ 373/493)
    (htlo : 11*σ/6-7/30 ≤ t) (hthi : t ≤ 6/5) :
    ((21/8)*(0)+(1/4))*t+((1-2*σ)*(1/2)+(21/8)*(18/5-4*σ)) ≤ energyClauseFourSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (11*σ/6-7/30) (6/5) t
    ((21/8)*(0)+(1/4)) ((1-2*σ)*(1/2)+(21/8)*(18/5-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFourSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(409/541))
      (by linarith : 0 ≤ (373/493)-σ)]

theorem energyClauseFour_high_8_0 {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : 1 ≤ t) (hthi : t ≤ (23*σ-11)/6) :
    ((9/5)*(0)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(2-2*σ)) ≤ energyClauseFourSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((23*σ-11)/6) t
    ((9/5)*(0)+(4/5)) (((8-16*σ)/5)*(1/2)+(9/5)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFourSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(409/541))
      (by linarith : 0 ≤ (373/493)-σ)]

theorem energyClauseFour_high_8_1 {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : (23*σ-11)/6 ≤ t) (hthi : t ≤ 11*σ/6-7/30) :
    ((9/5)*(1)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(23/6-(35/6)*σ)) ≤ energyClauseFourSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((23*σ-11)/6) (11*σ/6-7/30) t
    ((9/5)*(1)+(4/5)) (((8-16*σ)/5)*(1/2)+(9/5)*(23/6-(35/6)*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFourSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(409/541))
      (by linarith : 0 ≤ (373/493)-σ)]

theorem energyClauseFour_high_8_2 {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : 11*σ/6-7/30 ≤ t) (hthi : t ≤ 6/5) :
    ((9/5)*(0)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(18/5-4*σ)) ≤ energyClauseFourSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (11*σ/6-7/30) (6/5) t
    ((9/5)*(0)+(4/5)) (((8-16*σ)/5)*(1/2)+(9/5)*(18/5-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFourSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(409/541))
      (by linarith : 0 ≤ (373/493)-σ)]

end TaoTrudgianYang2025
