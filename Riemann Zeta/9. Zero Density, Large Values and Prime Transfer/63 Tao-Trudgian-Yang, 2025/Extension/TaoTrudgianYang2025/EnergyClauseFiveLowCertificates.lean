import TaoTrudgianYang2025.EnergyClauseFiveRates

/-!
# Exact low-sigma short-height certificates for Add-est (v)

All nine Heath--Brown branches and three closed height pieces
are bounded by the printed first or second rational rate.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem energyClauseFive_low_0_0 {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 1 ≤ t) (hthi : t ≤ 86*σ-64) :
    ((1)*(0)+(0))*t+((4-4*σ)*(2/3)+(1)*(2-2*σ)) ≤ energyClauseFiveSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (86*σ-64) t
    ((1)*(0)+(0)) ((4-4*σ)*(2/3)+(1)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(373/493))
      (by linarith : 0 ≤ (171/226)-σ)]

theorem energyClauseFive_low_0_1 {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 86*σ-64 ≤ t) (hthi : t ≤ 84*σ-312/5) :
    ((1)*(1)+(0))*t+((4-4*σ)*(2/3)+(1)*(66-88*σ)) ≤ energyClauseFiveSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (86*σ-64) (84*σ-312/5) t
    ((1)*(1)+(0)) ((4-4*σ)*(2/3)+(1)*(66-88*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(373/493))
      (by linarith : 0 ≤ (171/226)-σ)]

theorem energyClauseFive_low_0_2 {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 84*σ-312/5 ≤ t) (hthi : t ≤ 6/5) :
    ((1)*(0)+(0))*t+((4-4*σ)*(2/3)+(1)*(18/5-4*σ)) ≤ energyClauseFiveSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (84*σ-312/5) (6/5) t
    ((1)*(0)+(0)) ((4-4*σ)*(2/3)+(1)*(18/5-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(373/493))
      (by linarith : 0 ≤ (171/226)-σ)]

theorem energyClauseFive_low_1_0 {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 1 ≤ t) (hthi : t ≤ 86*σ-64) :
    ((5/2)*(0)+(0))*t+(((3-4*σ)/2)*(1/2)+(5/2)*(2-2*σ)) ≤ energyClauseFiveSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (86*σ-64) t
    ((5/2)*(0)+(0)) (((3-4*σ)/2)*(1/2)+(5/2)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(373/493))
      (by linarith : 0 ≤ (171/226)-σ)]

theorem energyClauseFive_low_1_1 {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 86*σ-64 ≤ t) (hthi : t ≤ 84*σ-312/5) :
    ((5/2)*(1)+(0))*t+(((3-4*σ)/2)*(1/2)+(5/2)*(66-88*σ)) ≤ energyClauseFiveSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (86*σ-64) (84*σ-312/5) t
    ((5/2)*(1)+(0)) (((3-4*σ)/2)*(1/2)+(5/2)*(66-88*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(373/493))
      (by linarith : 0 ≤ (171/226)-σ)]

theorem energyClauseFive_low_1_2 {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 84*σ-312/5 ≤ t) (hthi : t ≤ 6/5) :
    ((5/2)*(0)+(0))*t+(((3-4*σ)/2)*(1/2)+(5/2)*(18/5-4*σ)) ≤ energyClauseFiveSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (84*σ-312/5) (6/5) t
    ((5/2)*(0)+(0)) (((3-4*σ)/2)*(1/2)+(5/2)*(18/5-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(373/493))
      (by linarith : 0 ≤ (171/226)-σ)]

theorem energyClauseFive_low_2_0 {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 1 ≤ t) (hthi : t ≤ 86*σ-64) :
    ((8/5)*(0)+(2/5))*t+(((12-16*σ)/5)*(1/2)+(8/5)*(2-2*σ)) ≤ energyClauseFiveSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (86*σ-64) t
    ((8/5)*(0)+(2/5)) (((12-16*σ)/5)*(1/2)+(8/5)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(373/493))
      (by linarith : 0 ≤ (171/226)-σ)]

theorem energyClauseFive_low_2_1 {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 86*σ-64 ≤ t) (hthi : t ≤ 84*σ-312/5) :
    ((8/5)*(1)+(2/5))*t+(((12-16*σ)/5)*(1/2)+(8/5)*(66-88*σ)) ≤ energyClauseFiveSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (86*σ-64) (84*σ-312/5) t
    ((8/5)*(1)+(2/5)) (((12-16*σ)/5)*(1/2)+(8/5)*(66-88*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(373/493))
      (by linarith : 0 ≤ (171/226)-σ)]

theorem energyClauseFive_low_2_2 {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 84*σ-312/5 ≤ t) (hthi : t ≤ 6/5) :
    ((8/5)*(0)+(2/5))*t+(((12-16*σ)/5)*(1/2)+(8/5)*(18/5-4*σ)) ≤ energyClauseFiveSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (84*σ-312/5) (6/5) t
    ((8/5)*(0)+(2/5)) (((12-16*σ)/5)*(1/2)+(8/5)*(18/5-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(373/493))
      (by linarith : 0 ≤ (171/226)-σ)]

theorem energyClauseFive_low_3_0 {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 1 ≤ t) (hthi : t ≤ 86*σ-64) :
    ((2)*(0)+(0))*t+((3-4*σ)*(1/2)+(2)*(2-2*σ)) ≤ energyClauseFiveSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (86*σ-64) t
    ((2)*(0)+(0)) ((3-4*σ)*(1/2)+(2)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(373/493))
      (by linarith : 0 ≤ (171/226)-σ)]

theorem energyClauseFive_low_3_1 {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 86*σ-64 ≤ t) (hthi : t ≤ 84*σ-312/5) :
    ((2)*(1)+(0))*t+((3-4*σ)*(1/2)+(2)*(66-88*σ)) ≤ energyClauseFiveSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (86*σ-64) (84*σ-312/5) t
    ((2)*(1)+(0)) ((3-4*σ)*(1/2)+(2)*(66-88*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(373/493))
      (by linarith : 0 ≤ (171/226)-σ)]

theorem energyClauseFive_low_3_2 {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 84*σ-312/5 ≤ t) (hthi : t ≤ 6/5) :
    ((2)*(0)+(0))*t+((3-4*σ)*(1/2)+(2)*(18/5-4*σ)) ≤ energyClauseFiveSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (84*σ-312/5) (6/5) t
    ((2)*(0)+(0)) ((3-4*σ)*(1/2)+(2)*(18/5-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(373/493))
      (by linarith : 0 ≤ (171/226)-σ)]

theorem energyClauseFive_low_4_0 {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 1 ≤ t) (hthi : t ≤ 86*σ-64) :
    ((3)*(0)+(0))*t+((1-2*σ)*(1/2)+(3)*(2-2*σ)) ≤ energyClauseFiveSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (86*σ-64) t
    ((3)*(0)+(0)) ((1-2*σ)*(1/2)+(3)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(373/493))
      (by linarith : 0 ≤ (171/226)-σ)]

theorem energyClauseFive_low_4_1 {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 86*σ-64 ≤ t) (hthi : t ≤ 84*σ-312/5) :
    ((3)*(1)+(0))*t+((1-2*σ)*(1/2)+(3)*(66-88*σ)) ≤ energyClauseFiveSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (86*σ-64) (84*σ-312/5) t
    ((3)*(1)+(0)) ((1-2*σ)*(1/2)+(3)*(66-88*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(373/493))
      (by linarith : 0 ≤ (171/226)-σ)]

theorem energyClauseFive_low_4_2 {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 84*σ-312/5 ≤ t) (hthi : t ≤ 6/5) :
    ((3)*(0)+(0))*t+((1-2*σ)*(1/2)+(3)*(18/5-4*σ)) ≤ energyClauseFiveSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (84*σ-312/5) (6/5) t
    ((3)*(0)+(0)) ((1-2*σ)*(1/2)+(3)*(18/5-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(373/493))
      (by linarith : 0 ≤ (171/226)-σ)]

theorem energyClauseFive_low_5_0 {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 1 ≤ t) (hthi : t ≤ 86*σ-64) :
    ((12/5)*(0)+(2/5))*t+(((8-16*σ)/5)*(1/2)+(12/5)*(2-2*σ)) ≤ energyClauseFiveSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (86*σ-64) t
    ((12/5)*(0)+(2/5)) (((8-16*σ)/5)*(1/2)+(12/5)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(373/493))
      (by linarith : 0 ≤ (171/226)-σ)]

theorem energyClauseFive_low_5_1 {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 86*σ-64 ≤ t) (hthi : t ≤ 84*σ-312/5) :
    ((12/5)*(1)+(2/5))*t+(((8-16*σ)/5)*(1/2)+(12/5)*(66-88*σ)) ≤ energyClauseFiveSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (86*σ-64) (84*σ-312/5) t
    ((12/5)*(1)+(2/5)) (((8-16*σ)/5)*(1/2)+(12/5)*(66-88*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(373/493))
      (by linarith : 0 ≤ (171/226)-σ)]

theorem energyClauseFive_low_5_2 {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 84*σ-312/5 ≤ t) (hthi : t ≤ 6/5) :
    ((12/5)*(0)+(2/5))*t+(((8-16*σ)/5)*(1/2)+(12/5)*(18/5-4*σ)) ≤ energyClauseFiveSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (84*σ-312/5) (6/5) t
    ((12/5)*(0)+(2/5)) (((8-16*σ)/5)*(1/2)+(12/5)*(18/5-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(373/493))
      (by linarith : 0 ≤ (171/226)-σ)]

theorem energyClauseFive_low_6_0 {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 1 ≤ t) (hthi : t ≤ 86*σ-64) :
    ((5/4)*(0)+(1/2))*t+((3-4*σ)*(1/2)+(5/4)*(2-2*σ)) ≤ energyClauseFiveSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (86*σ-64) t
    ((5/4)*(0)+(1/2)) ((3-4*σ)*(1/2)+(5/4)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(373/493))
      (by linarith : 0 ≤ (171/226)-σ)]

theorem energyClauseFive_low_6_1 {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 86*σ-64 ≤ t) (hthi : t ≤ 84*σ-312/5) :
    ((5/4)*(1)+(1/2))*t+((3-4*σ)*(1/2)+(5/4)*(66-88*σ)) ≤ energyClauseFiveSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (86*σ-64) (84*σ-312/5) t
    ((5/4)*(1)+(1/2)) ((3-4*σ)*(1/2)+(5/4)*(66-88*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(373/493))
      (by linarith : 0 ≤ (171/226)-σ)]

theorem energyClauseFive_low_6_2 {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 84*σ-312/5 ≤ t) (hthi : t ≤ 6/5) :
    ((5/4)*(0)+(1/2))*t+((3-4*σ)*(1/2)+(5/4)*(18/5-4*σ)) ≤ energyClauseFiveSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (84*σ-312/5) (6/5) t
    ((5/4)*(0)+(1/2)) ((3-4*σ)*(1/2)+(5/4)*(18/5-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(373/493))
      (by linarith : 0 ≤ (171/226)-σ)]

theorem energyClauseFive_low_7_0 {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 1 ≤ t) (hthi : t ≤ 86*σ-64) :
    ((21/8)*(0)+(1/4))*t+((1-2*σ)*(1/2)+(21/8)*(2-2*σ)) ≤ energyClauseFiveSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (86*σ-64) t
    ((21/8)*(0)+(1/4)) ((1-2*σ)*(1/2)+(21/8)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(373/493))
      (by linarith : 0 ≤ (171/226)-σ)]

theorem energyClauseFive_low_7_1 {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 86*σ-64 ≤ t) (hthi : t ≤ 84*σ-312/5) :
    ((21/8)*(1)+(1/4))*t+((1-2*σ)*(1/2)+(21/8)*(66-88*σ)) ≤ energyClauseFiveSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (86*σ-64) (84*σ-312/5) t
    ((21/8)*(1)+(1/4)) ((1-2*σ)*(1/2)+(21/8)*(66-88*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(373/493))
      (by linarith : 0 ≤ (171/226)-σ)]

theorem energyClauseFive_low_7_2 {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 84*σ-312/5 ≤ t) (hthi : t ≤ 6/5) :
    ((21/8)*(0)+(1/4))*t+((1-2*σ)*(1/2)+(21/8)*(18/5-4*σ)) ≤ energyClauseFiveSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (84*σ-312/5) (6/5) t
    ((21/8)*(0)+(1/4)) ((1-2*σ)*(1/2)+(21/8)*(18/5-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(373/493))
      (by linarith : 0 ≤ (171/226)-σ)]

theorem energyClauseFive_low_8_0 {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 1 ≤ t) (hthi : t ≤ 86*σ-64) :
    ((9/5)*(0)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(2-2*σ)) ≤ energyClauseFiveFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (86*σ-64) t
    ((9/5)*(0)+(4/5)) (((8-16*σ)/5)*(1/2)+(9/5)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(373/493))
      (by linarith : 0 ≤ (171/226)-σ)]

theorem energyClauseFive_low_8_1 {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 86*σ-64 ≤ t) (hthi : t ≤ 84*σ-312/5) :
    ((9/5)*(1)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(66-88*σ)) ≤ energyClauseFiveFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (86*σ-64) (84*σ-312/5) t
    ((9/5)*(1)+(4/5)) (((8-16*σ)/5)*(1/2)+(9/5)*(66-88*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(373/493))
      (by linarith : 0 ≤ (171/226)-σ)]

theorem energyClauseFive_low_8_2 {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 84*σ-312/5 ≤ t) (hthi : t ≤ 6/5) :
    ((9/5)*(0)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(18/5-4*σ)) ≤ energyClauseFiveFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (84*σ-312/5) (6/5) t
    ((9/5)*(0)+(4/5)) (((8-16*σ)/5)*(1/2)+(9/5)*(18/5-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseFiveFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(373/493))
      (by linarith : 0 ≤ (171/226)-σ)]

end TaoTrudgianYang2025
