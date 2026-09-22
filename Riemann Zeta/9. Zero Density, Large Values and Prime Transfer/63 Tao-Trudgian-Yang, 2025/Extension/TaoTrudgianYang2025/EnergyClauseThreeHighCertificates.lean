import TaoTrudgianYang2025.EnergyClauseThreeRates

/-!
# Exact high-sigma short-height certificates for Add-est (iii)

Every comparison is proved over its full closed interval by rational
algebra in Lean. Numerical exploration supplies no proof evidence.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem energyClauseThree_high_0_0 {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : 1 ≤ t) (hthi : t ≤ (50*σ-24)/13) :
    ((1)*(0)+(0))*t+((4-4*σ)*(2/3)+(1)*(2-2*σ)) ≤ energyClauseThreeThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((50*σ-24)/13) t
    ((1)*(0)+(0)) ((4-4*σ)*(2/3)+(1)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(241/319))
      (by linarith : 0 ≤ (443/586)-σ)]

theorem energyClauseThree_high_0_1 {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : (50*σ-24)/13 ≤ t) (hthi : t ≤ 8*(15*σ-2)/65) :
    ((1)*(1)+(0))*t+((4-4*σ)*(2/3)+(1)*(50/13-(76/13)*σ)) ≤ energyClauseThreeThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((50*σ-24)/13) (8*(15*σ-2)/65) t
    ((1)*(1)+(0)) ((4-4*σ)*(2/3)+(1)*(50/13-(76/13)*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(241/319))
      (by linarith : 0 ≤ (443/586)-σ)]

theorem energyClauseThree_high_0_2 {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : 8*(15*σ-2)/65 ≤ t) (hthi : t ≤ 6/5) :
    ((1)*(0)+(0))*t+((4-4*σ)*(2/3)+(1)*(18/5-4*σ)) ≤ energyClauseThreeThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (8*(15*σ-2)/65) (6/5) t
    ((1)*(0)+(0)) ((4-4*σ)*(2/3)+(1)*(18/5-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(241/319))
      (by linarith : 0 ≤ (443/586)-σ)]

theorem energyClauseThree_high_1_0 {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : 1 ≤ t) (hthi : t ≤ (50*σ-24)/13) :
    ((5/2)*(0)+(0))*t+(((3-4*σ)/2)*(1/2)+(5/2)*(2-2*σ)) ≤ energyClauseThreeThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((50*σ-24)/13) t
    ((5/2)*(0)+(0)) (((3-4*σ)/2)*(1/2)+(5/2)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(241/319))
      (by linarith : 0 ≤ (443/586)-σ)]

theorem energyClauseThree_high_1_1 {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : (50*σ-24)/13 ≤ t) (hthi : t ≤ 8*(15*σ-2)/65) :
    ((5/2)*(1)+(0))*t+(((3-4*σ)/2)*(1/2)+(5/2)*(50/13-(76/13)*σ)) ≤ energyClauseThreeThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((50*σ-24)/13) (8*(15*σ-2)/65) t
    ((5/2)*(1)+(0)) (((3-4*σ)/2)*(1/2)+(5/2)*(50/13-(76/13)*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(241/319))
      (by linarith : 0 ≤ (443/586)-σ)]

theorem energyClauseThree_high_1_2 {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (_hhi : σ ≤ 443/586)
    (htlo : 8*(15*σ-2)/65 ≤ t) (hthi : t ≤ 6/5) :
    ((5/2)*(0)+(0))*t+(((3-4*σ)/2)*(1/2)+(5/2)*(18/5-4*σ)) ≤ energyClauseThreeThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (8*(15*σ-2)/65) (6/5) t
    ((5/2)*(0)+(0)) (((3-4*σ)/2)*(1/2)+(5/2)*(18/5-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(241/319))
      (by linarith : 0 ≤ (443/586)-σ)]

theorem energyClauseThree_high_2_0 {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : 1 ≤ t) (hthi : t ≤ (50*σ-24)/13) :
    ((8/5)*(0)+(2/5))*t+(((12-16*σ)/5)*(1/2)+(8/5)*(2-2*σ)) ≤ energyClauseThreeThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((50*σ-24)/13) t
    ((8/5)*(0)+(2/5)) (((12-16*σ)/5)*(1/2)+(8/5)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(241/319))
      (by linarith : 0 ≤ (443/586)-σ)]

theorem energyClauseThree_high_2_1 {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : (50*σ-24)/13 ≤ t) (hthi : t ≤ 8*(15*σ-2)/65) :
    ((8/5)*(1)+(2/5))*t+(((12-16*σ)/5)*(1/2)+(8/5)*(50/13-(76/13)*σ)) ≤ energyClauseThreeThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((50*σ-24)/13) (8*(15*σ-2)/65) t
    ((8/5)*(1)+(2/5)) (((12-16*σ)/5)*(1/2)+(8/5)*(50/13-(76/13)*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(241/319))
      (by linarith : 0 ≤ (443/586)-σ)]

theorem energyClauseThree_high_2_2 {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : 8*(15*σ-2)/65 ≤ t) (hthi : t ≤ 6/5) :
    ((8/5)*(0)+(2/5))*t+(((12-16*σ)/5)*(1/2)+(8/5)*(18/5-4*σ)) ≤ energyClauseThreeThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (8*(15*σ-2)/65) (6/5) t
    ((8/5)*(0)+(2/5)) (((12-16*σ)/5)*(1/2)+(8/5)*(18/5-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(241/319))
      (by linarith : 0 ≤ (443/586)-σ)]

theorem energyClauseThree_high_3_0 {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : 1 ≤ t) (hthi : t ≤ (50*σ-24)/13) :
    ((2)*(0)+(0))*t+((3-4*σ)*(1/2)+(2)*(2-2*σ)) ≤ energyClauseThreeThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((50*σ-24)/13) t
    ((2)*(0)+(0)) ((3-4*σ)*(1/2)+(2)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(241/319))
      (by linarith : 0 ≤ (443/586)-σ)]

theorem energyClauseThree_high_3_1 {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : (50*σ-24)/13 ≤ t) (hthi : t ≤ 8*(15*σ-2)/65) :
    ((2)*(1)+(0))*t+((3-4*σ)*(1/2)+(2)*(50/13-(76/13)*σ)) ≤ energyClauseThreeThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((50*σ-24)/13) (8*(15*σ-2)/65) t
    ((2)*(1)+(0)) ((3-4*σ)*(1/2)+(2)*(50/13-(76/13)*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(241/319))
      (by linarith : 0 ≤ (443/586)-σ)]

theorem energyClauseThree_high_3_2 {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (_hhi : σ ≤ 443/586)
    (htlo : 8*(15*σ-2)/65 ≤ t) (hthi : t ≤ 6/5) :
    ((2)*(0)+(0))*t+((3-4*σ)*(1/2)+(2)*(18/5-4*σ)) ≤ energyClauseThreeThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (8*(15*σ-2)/65) (6/5) t
    ((2)*(0)+(0)) ((3-4*σ)*(1/2)+(2)*(18/5-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(241/319))
      (by linarith : 0 ≤ (443/586)-σ)]

theorem energyClauseThree_high_4_0 {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : 1 ≤ t) (hthi : t ≤ (50*σ-24)/13) :
    ((3)*(0)+(0))*t+((1-2*σ)*(1/2)+(3)*(2-2*σ)) ≤ energyClauseThreeThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((50*σ-24)/13) t
    ((3)*(0)+(0)) ((1-2*σ)*(1/2)+(3)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(241/319))
      (by linarith : 0 ≤ (443/586)-σ)]

theorem energyClauseThree_high_4_1 {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : (50*σ-24)/13 ≤ t) (hthi : t ≤ 8*(15*σ-2)/65) :
    ((3)*(1)+(0))*t+((1-2*σ)*(1/2)+(3)*(50/13-(76/13)*σ)) ≤ energyClauseThreeThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((50*σ-24)/13) (8*(15*σ-2)/65) t
    ((3)*(1)+(0)) ((1-2*σ)*(1/2)+(3)*(50/13-(76/13)*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(241/319))
      (by linarith : 0 ≤ (443/586)-σ)]

theorem energyClauseThree_high_4_2 {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (_hhi : σ ≤ 443/586)
    (htlo : 8*(15*σ-2)/65 ≤ t) (hthi : t ≤ 6/5) :
    ((3)*(0)+(0))*t+((1-2*σ)*(1/2)+(3)*(18/5-4*σ)) ≤ energyClauseThreeThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (8*(15*σ-2)/65) (6/5) t
    ((3)*(0)+(0)) ((1-2*σ)*(1/2)+(3)*(18/5-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(241/319))
      (by linarith : 0 ≤ (443/586)-σ)]

theorem energyClauseThree_high_5_0 {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : 1 ≤ t) (hthi : t ≤ (50*σ-24)/13) :
    ((12/5)*(0)+(2/5))*t+(((8-16*σ)/5)*(1/2)+(12/5)*(2-2*σ)) ≤ energyClauseThreeThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((50*σ-24)/13) t
    ((12/5)*(0)+(2/5)) (((8-16*σ)/5)*(1/2)+(12/5)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(241/319))
      (by linarith : 0 ≤ (443/586)-σ)]

theorem energyClauseThree_high_5_1 {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : (50*σ-24)/13 ≤ t) (hthi : t ≤ 8*(15*σ-2)/65) :
    ((12/5)*(1)+(2/5))*t+(((8-16*σ)/5)*(1/2)+(12/5)*(50/13-(76/13)*σ)) ≤ energyClauseThreeThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((50*σ-24)/13) (8*(15*σ-2)/65) t
    ((12/5)*(1)+(2/5)) (((8-16*σ)/5)*(1/2)+(12/5)*(50/13-(76/13)*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(241/319))
      (by linarith : 0 ≤ (443/586)-σ)]

theorem energyClauseThree_high_5_2 {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (_hhi : σ ≤ 443/586)
    (htlo : 8*(15*σ-2)/65 ≤ t) (hthi : t ≤ 6/5) :
    ((12/5)*(0)+(2/5))*t+(((8-16*σ)/5)*(1/2)+(12/5)*(18/5-4*σ)) ≤ energyClauseThreeThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (8*(15*σ-2)/65) (6/5) t
    ((12/5)*(0)+(2/5)) (((8-16*σ)/5)*(1/2)+(12/5)*(18/5-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(241/319))
      (by linarith : 0 ≤ (443/586)-σ)]

theorem energyClauseThree_high_6_0 {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : 1 ≤ t) (hthi : t ≤ (50*σ-24)/13) :
    ((5/4)*(0)+(1/2))*t+((3-4*σ)*(1/2)+(5/4)*(2-2*σ)) ≤ energyClauseThreeThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((50*σ-24)/13) t
    ((5/4)*(0)+(1/2)) ((3-4*σ)*(1/2)+(5/4)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(241/319))
      (by linarith : 0 ≤ (443/586)-σ)]

theorem energyClauseThree_high_6_1 {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : (50*σ-24)/13 ≤ t) (hthi : t ≤ 8*(15*σ-2)/65) :
    ((5/4)*(1)+(1/2))*t+((3-4*σ)*(1/2)+(5/4)*(50/13-(76/13)*σ)) ≤ energyClauseThreeThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((50*σ-24)/13) (8*(15*σ-2)/65) t
    ((5/4)*(1)+(1/2)) ((3-4*σ)*(1/2)+(5/4)*(50/13-(76/13)*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(241/319))
      (by linarith : 0 ≤ (443/586)-σ)]

theorem energyClauseThree_high_6_2 {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : 8*(15*σ-2)/65 ≤ t) (hthi : t ≤ 6/5) :
    ((5/4)*(0)+(1/2))*t+((3-4*σ)*(1/2)+(5/4)*(18/5-4*σ)) ≤ energyClauseThreeThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (8*(15*σ-2)/65) (6/5) t
    ((5/4)*(0)+(1/2)) ((3-4*σ)*(1/2)+(5/4)*(18/5-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(241/319))
      (by linarith : 0 ≤ (443/586)-σ)]

theorem energyClauseThree_high_7_0 {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : 1 ≤ t) (hthi : t ≤ (50*σ-24)/13) :
    ((21/8)*(0)+(1/4))*t+((1-2*σ)*(1/2)+(21/8)*(2-2*σ)) ≤ energyClauseThreeThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((50*σ-24)/13) t
    ((21/8)*(0)+(1/4)) ((1-2*σ)*(1/2)+(21/8)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(241/319))
      (by linarith : 0 ≤ (443/586)-σ)]

theorem energyClauseThree_high_7_1 {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : (50*σ-24)/13 ≤ t) (hthi : t ≤ 8*(15*σ-2)/65) :
    ((21/8)*(1)+(1/4))*t+((1-2*σ)*(1/2)+(21/8)*(50/13-(76/13)*σ)) ≤ energyClauseThreeThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((50*σ-24)/13) (8*(15*σ-2)/65) t
    ((21/8)*(1)+(1/4)) ((1-2*σ)*(1/2)+(21/8)*(50/13-(76/13)*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(241/319))
      (by linarith : 0 ≤ (443/586)-σ)]

theorem energyClauseThree_high_7_2 {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (_hhi : σ ≤ 443/586)
    (htlo : 8*(15*σ-2)/65 ≤ t) (hthi : t ≤ 6/5) :
    ((21/8)*(0)+(1/4))*t+((1-2*σ)*(1/2)+(21/8)*(18/5-4*σ)) ≤ energyClauseThreeThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (8*(15*σ-2)/65) (6/5) t
    ((21/8)*(0)+(1/4)) ((1-2*σ)*(1/2)+(21/8)*(18/5-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(241/319))
      (by linarith : 0 ≤ (443/586)-σ)]

theorem energyClauseThree_high_8_0 {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : 1 ≤ t) (hthi : t ≤ (50*σ-24)/13) :
    ((9/5)*(0)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(2-2*σ)) ≤ energyClauseThreeThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) ((50*σ-24)/13) t
    ((9/5)*(0)+(4/5)) (((8-16*σ)/5)*(1/2)+(9/5)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(241/319))
      (by linarith : 0 ≤ (443/586)-σ)]

theorem energyClauseThree_high_8_1 {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : (50*σ-24)/13 ≤ t) (hthi : t ≤ 8*(15*σ-2)/65) :
    ((9/5)*(1)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(50/13-(76/13)*σ)) ≤ energyClauseThreeThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((50*σ-24)/13) (8*(15*σ-2)/65) t
    ((9/5)*(1)+(4/5)) (((8-16*σ)/5)*(1/2)+(9/5)*(50/13-(76/13)*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(241/319))
      (by linarith : 0 ≤ (443/586)-σ)]

theorem energyClauseThree_high_8_2 {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : 8*(15*σ-2)/65 ≤ t) (hthi : t ≤ 6/5) :
    ((9/5)*(0)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(18/5-4*σ)) ≤ energyClauseThreeThirdRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (8*(15*σ-2)/65) (6/5) t
    ((9/5)*(0)+(4/5)) (((8-16*σ)/5)*(1/2)+(9/5)*(18/5-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeThirdRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(241/319))
      (by linarith : 0 ≤ (443/586)-σ)]

end TaoTrudgianYang2025
