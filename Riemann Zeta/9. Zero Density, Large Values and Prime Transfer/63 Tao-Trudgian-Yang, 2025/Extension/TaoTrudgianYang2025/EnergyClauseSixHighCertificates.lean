import TaoTrudgianYang2025.EnergyClauseSixRates

/-!
# Exact high-sigma short-height certificates for Add-est (vi)

All nine independent-power Heath--Brown branches are bounded on
the full blueprint sigma interval and both closed height pieces.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem energyClauseSix_high_0_0 {σ t : ℝ}
    (hlo : 281/371 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : 1 ≤ t) (hthi : t ≤ (19*σ-9)/5) :
    ((1)*(0)+(0))*t+((4-4*σ)*(2/3)+(1)*(2-2*σ)) ≤ energyClauseSixSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((19*σ-9)/5) t
    ((1)*(0)+(0)) ((4-4*σ)*(2/3)+(1)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSixSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(281/371))
      (by linarith : 0 ≤ (31/40)-σ)]

theorem energyClauseSix_high_0_1 {σ t : ℝ}
    (hlo : 281/371 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : (19*σ-9)/5 ≤ t) (hthi : t ≤ (14*σ+1)/10) :
    ((1)*(1)+(0))*t+((4-4*σ)*(2/3)+(1)*(19/5-(29/5)*σ)) ≤ energyClauseSixSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((19*σ-9)/5) ((14*σ+1)/10) t
    ((1)*(1)+(0)) ((4-4*σ)*(2/3)+(1)*(19/5-(29/5)*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSixSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(281/371))
      (by linarith : 0 ≤ (31/40)-σ)]

theorem energyClauseSix_high_1_0 {σ t : ℝ}
    (hlo : 281/371 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : 1 ≤ t) (hthi : t ≤ (19*σ-9)/5) :
    ((5/2)*(0)+(0))*t+(((3-4*σ)/2)*(1/2)+(5/2)*(2-2*σ)) ≤ energyClauseSixSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((19*σ-9)/5) t
    ((5/2)*(0)+(0)) (((3-4*σ)/2)*(1/2)+(5/2)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSixSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(281/371))
      (by linarith : 0 ≤ (31/40)-σ)]

theorem energyClauseSix_high_1_1 {σ t : ℝ}
    (hlo : 281/371 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : (19*σ-9)/5 ≤ t) (hthi : t ≤ (14*σ+1)/10) :
    ((5/2)*(1)+(0))*t+(((3-4*σ)/2)*(1/2)+(5/2)*(19/5-(29/5)*σ)) ≤ energyClauseSixSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((19*σ-9)/5) ((14*σ+1)/10) t
    ((5/2)*(1)+(0)) (((3-4*σ)/2)*(1/2)+(5/2)*(19/5-(29/5)*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSixSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(281/371))
      (by linarith : 0 ≤ (31/40)-σ)]

theorem energyClauseSix_high_2_0 {σ t : ℝ}
    (hlo : 281/371 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : 1 ≤ t) (hthi : t ≤ (19*σ-9)/5) :
    ((8/5)*(0)+(2/5))*t+(((12-16*σ)/5)*(1/2)+(8/5)*(2-2*σ)) ≤ energyClauseSixSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((19*σ-9)/5) t
    ((8/5)*(0)+(2/5)) (((12-16*σ)/5)*(1/2)+(8/5)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSixSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(281/371))
      (by linarith : 0 ≤ (31/40)-σ)]

theorem energyClauseSix_high_2_1 {σ t : ℝ}
    (hlo : 281/371 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : (19*σ-9)/5 ≤ t) (hthi : t ≤ (14*σ+1)/10) :
    ((8/5)*(1)+(2/5))*t+(((12-16*σ)/5)*(1/2)+(8/5)*(19/5-(29/5)*σ)) ≤ energyClauseSixSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((19*σ-9)/5) ((14*σ+1)/10) t
    ((8/5)*(1)+(2/5)) (((12-16*σ)/5)*(1/2)+(8/5)*(19/5-(29/5)*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSixSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(281/371))
      (by linarith : 0 ≤ (31/40)-σ)]

theorem energyClauseSix_high_3_0 {σ t : ℝ}
    (hlo : 281/371 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : 1 ≤ t) (hthi : t ≤ (19*σ-9)/5) :
    ((2)*(0)+(0))*t+((3-4*σ)*(1/2)+(2)*(2-2*σ)) ≤ energyClauseSixSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((19*σ-9)/5) t
    ((2)*(0)+(0)) ((3-4*σ)*(1/2)+(2)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSixSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(281/371))
      (by linarith : 0 ≤ (31/40)-σ)]

theorem energyClauseSix_high_3_1 {σ t : ℝ}
    (hlo : 281/371 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : (19*σ-9)/5 ≤ t) (hthi : t ≤ (14*σ+1)/10) :
    ((2)*(1)+(0))*t+((3-4*σ)*(1/2)+(2)*(19/5-(29/5)*σ)) ≤ energyClauseSixSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((19*σ-9)/5) ((14*σ+1)/10) t
    ((2)*(1)+(0)) ((3-4*σ)*(1/2)+(2)*(19/5-(29/5)*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSixSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(281/371))
      (by linarith : 0 ≤ (31/40)-σ)]

theorem energyClauseSix_high_4_0 {σ t : ℝ}
    (hlo : 281/371 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : 1 ≤ t) (hthi : t ≤ (19*σ-9)/5) :
    ((3)*(0)+(0))*t+((1-2*σ)*(1/2)+(3)*(2-2*σ)) ≤ energyClauseSixSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((19*σ-9)/5) t
    ((3)*(0)+(0)) ((1-2*σ)*(1/2)+(3)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSixSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(281/371))
      (by linarith : 0 ≤ (31/40)-σ)]

theorem energyClauseSix_high_4_1 {σ t : ℝ}
    (hlo : 281/371 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : (19*σ-9)/5 ≤ t) (hthi : t ≤ (14*σ+1)/10) :
    ((3)*(1)+(0))*t+((1-2*σ)*(1/2)+(3)*(19/5-(29/5)*σ)) ≤ energyClauseSixSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((19*σ-9)/5) ((14*σ+1)/10) t
    ((3)*(1)+(0)) ((1-2*σ)*(1/2)+(3)*(19/5-(29/5)*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSixSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(281/371))
      (by linarith : 0 ≤ (31/40)-σ)]

theorem energyClauseSix_high_5_0 {σ t : ℝ}
    (hlo : 281/371 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : 1 ≤ t) (hthi : t ≤ (19*σ-9)/5) :
    ((12/5)*(0)+(2/5))*t+(((8-16*σ)/5)*(1/2)+(12/5)*(2-2*σ)) ≤ energyClauseSixSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((19*σ-9)/5) t
    ((12/5)*(0)+(2/5)) (((8-16*σ)/5)*(1/2)+(12/5)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSixSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(281/371))
      (by linarith : 0 ≤ (31/40)-σ)]

theorem energyClauseSix_high_5_1 {σ t : ℝ}
    (hlo : 281/371 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : (19*σ-9)/5 ≤ t) (hthi : t ≤ (14*σ+1)/10) :
    ((12/5)*(1)+(2/5))*t+(((8-16*σ)/5)*(1/2)+(12/5)*(19/5-(29/5)*σ)) ≤ energyClauseSixSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((19*σ-9)/5) ((14*σ+1)/10) t
    ((12/5)*(1)+(2/5)) (((8-16*σ)/5)*(1/2)+(12/5)*(19/5-(29/5)*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSixSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(281/371))
      (by linarith : 0 ≤ (31/40)-σ)]

theorem energyClauseSix_high_6_0 {σ t : ℝ}
    (hlo : 281/371 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : 1 ≤ t) (hthi : t ≤ (19*σ-9)/5) :
    ((5/4)*(0)+(1/2))*t+((3-4*σ)*(1/2)+(5/4)*(2-2*σ)) ≤ energyClauseSixSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((19*σ-9)/5) t
    ((5/4)*(0)+(1/2)) ((3-4*σ)*(1/2)+(5/4)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSixSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(281/371))
      (by linarith : 0 ≤ (31/40)-σ)]

theorem energyClauseSix_high_6_1 {σ t : ℝ}
    (hlo : 281/371 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : (19*σ-9)/5 ≤ t) (hthi : t ≤ (14*σ+1)/10) :
    ((5/4)*(1)+(1/2))*t+((3-4*σ)*(1/2)+(5/4)*(19/5-(29/5)*σ)) ≤ energyClauseSixSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((19*σ-9)/5) ((14*σ+1)/10) t
    ((5/4)*(1)+(1/2)) ((3-4*σ)*(1/2)+(5/4)*(19/5-(29/5)*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSixSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(281/371))
      (by linarith : 0 ≤ (31/40)-σ)]

theorem energyClauseSix_high_7_0 {σ t : ℝ}
    (hlo : 281/371 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : 1 ≤ t) (hthi : t ≤ (19*σ-9)/5) :
    ((21/8)*(0)+(1/4))*t+((1-2*σ)*(1/2)+(21/8)*(2-2*σ)) ≤ energyClauseSixSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((19*σ-9)/5) t
    ((21/8)*(0)+(1/4)) ((1-2*σ)*(1/2)+(21/8)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSixSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(281/371))
      (by linarith : 0 ≤ (31/40)-σ)]

theorem energyClauseSix_high_7_1 {σ t : ℝ}
    (hlo : 281/371 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : (19*σ-9)/5 ≤ t) (hthi : t ≤ (14*σ+1)/10) :
    ((21/8)*(1)+(1/4))*t+((1-2*σ)*(1/2)+(21/8)*(19/5-(29/5)*σ)) ≤ energyClauseSixSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((19*σ-9)/5) ((14*σ+1)/10) t
    ((21/8)*(1)+(1/4)) ((1-2*σ)*(1/2)+(21/8)*(19/5-(29/5)*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSixSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(281/371))
      (by linarith : 0 ≤ (31/40)-σ)]

theorem energyClauseSix_high_8_0 {σ t : ℝ}
    (hlo : 281/371 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : 1 ≤ t) (hthi : t ≤ (19*σ-9)/5) :
    ((9/5)*(0)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(2-2*σ)) ≤ energyClauseSixSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((19*σ-9)/5) t
    ((9/5)*(0)+(4/5)) (((8-16*σ)/5)*(1/2)+(9/5)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSixSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(281/371))
      (by linarith : 0 ≤ (31/40)-σ)]

theorem energyClauseSix_high_8_1 {σ t : ℝ}
    (hlo : 281/371 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : (19*σ-9)/5 ≤ t) (hthi : t ≤ (14*σ+1)/10) :
    ((9/5)*(1)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(19/5-(29/5)*σ)) ≤ energyClauseSixSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((19*σ-9)/5) ((14*σ+1)/10) t
    ((9/5)*(1)+(4/5)) (((8-16*σ)/5)*(1/2)+(9/5)*(19/5-(29/5)*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSixSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(281/371))
      (by linarith : 0 ≤ (31/40)-σ)]

end TaoTrudgianYang2025
