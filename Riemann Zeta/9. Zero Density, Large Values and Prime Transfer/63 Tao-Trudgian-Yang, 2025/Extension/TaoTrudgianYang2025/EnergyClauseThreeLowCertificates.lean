import TaoTrudgianYang2025.EnergyClauseThreeRates

/-!
# Exact low-sigma short-height certificates for Add-est (iii)

Every comparison is proved over its full closed interval by rational
algebra in Lean. Numerical exploration supplies no proof evidence.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem energyClauseThree_low_0_0 {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 241/319)
    (htlo : 1 ≤ t) (hthi : t ≤ 102*σ-76) :
    ((1)*(0)+(0))*t+((4-4*σ)*(2/3)+(1)*(2-2*σ)) ≤ energyClauseThreeSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (102*σ-76) t
    ((1)*(0)+(0)) ((4-4*σ)*(2/3)+(1)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(173/229))
      (by linarith : 0 ≤ (241/319)-σ)]

theorem energyClauseThree_low_0_1 {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (_hhi : σ ≤ 241/319)
    (htlo : 102*σ-76 ≤ t) (hthi : t ≤ 100*σ-372/5) :
    ((1)*(1)+(0))*t+((4-4*σ)*(2/3)+(1)*(78-104*σ)) ≤ energyClauseThreeSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (102*σ-76) (100*σ-372/5) t
    ((1)*(1)+(0)) ((4-4*σ)*(2/3)+(1)*(78-104*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(173/229))
      (by linarith : 0 ≤ (241/319)-σ)]

theorem energyClauseThree_low_0_2 {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 241/319)
    (htlo : 100*σ-372/5 ≤ t) (hthi : t ≤ 6/5) :
    ((1)*(0)+(0))*t+((4-4*σ)*(2/3)+(1)*(18/5-4*σ)) ≤ energyClauseThreeSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (100*σ-372/5) (6/5) t
    ((1)*(0)+(0)) ((4-4*σ)*(2/3)+(1)*(18/5-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(173/229))
      (by linarith : 0 ≤ (241/319)-σ)]

theorem energyClauseThree_low_1_0 {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 241/319)
    (htlo : 1 ≤ t) (hthi : t ≤ 102*σ-76) :
    ((5/2)*(0)+(0))*t+(((3-4*σ)/2)*(1/2)+(5/2)*(2-2*σ)) ≤ energyClauseThreeSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (102*σ-76) t
    ((5/2)*(0)+(0)) (((3-4*σ)/2)*(1/2)+(5/2)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(173/229))
      (by linarith : 0 ≤ (241/319)-σ)]

theorem energyClauseThree_low_1_1 {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (_hhi : σ ≤ 241/319)
    (htlo : 102*σ-76 ≤ t) (hthi : t ≤ 100*σ-372/5) :
    ((5/2)*(1)+(0))*t+(((3-4*σ)/2)*(1/2)+(5/2)*(78-104*σ)) ≤ energyClauseThreeSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (102*σ-76) (100*σ-372/5) t
    ((5/2)*(1)+(0)) (((3-4*σ)/2)*(1/2)+(5/2)*(78-104*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(173/229))
      (by linarith : 0 ≤ (241/319)-σ)]

theorem energyClauseThree_low_1_2 {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 241/319)
    (htlo : 100*σ-372/5 ≤ t) (hthi : t ≤ 6/5) :
    ((5/2)*(0)+(0))*t+(((3-4*σ)/2)*(1/2)+(5/2)*(18/5-4*σ)) ≤ energyClauseThreeSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (100*σ-372/5) (6/5) t
    ((5/2)*(0)+(0)) (((3-4*σ)/2)*(1/2)+(5/2)*(18/5-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(173/229))
      (by linarith : 0 ≤ (241/319)-σ)]

theorem energyClauseThree_low_2_0 {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 241/319)
    (htlo : 1 ≤ t) (hthi : t ≤ 102*σ-76) :
    ((8/5)*(0)+(2/5))*t+(((12-16*σ)/5)*(1/2)+(8/5)*(2-2*σ)) ≤ energyClauseThreeSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (102*σ-76) t
    ((8/5)*(0)+(2/5)) (((12-16*σ)/5)*(1/2)+(8/5)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(173/229))
      (by linarith : 0 ≤ (241/319)-σ)]

theorem energyClauseThree_low_2_1 {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (_hhi : σ ≤ 241/319)
    (htlo : 102*σ-76 ≤ t) (hthi : t ≤ 100*σ-372/5) :
    ((8/5)*(1)+(2/5))*t+(((12-16*σ)/5)*(1/2)+(8/5)*(78-104*σ)) ≤ energyClauseThreeSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (102*σ-76) (100*σ-372/5) t
    ((8/5)*(1)+(2/5)) (((12-16*σ)/5)*(1/2)+(8/5)*(78-104*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(173/229))
      (by linarith : 0 ≤ (241/319)-σ)]

theorem energyClauseThree_low_2_2 {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 241/319)
    (htlo : 100*σ-372/5 ≤ t) (hthi : t ≤ 6/5) :
    ((8/5)*(0)+(2/5))*t+(((12-16*σ)/5)*(1/2)+(8/5)*(18/5-4*σ)) ≤ energyClauseThreeSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (100*σ-372/5) (6/5) t
    ((8/5)*(0)+(2/5)) (((12-16*σ)/5)*(1/2)+(8/5)*(18/5-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(173/229))
      (by linarith : 0 ≤ (241/319)-σ)]

theorem energyClauseThree_low_3_0 {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 241/319)
    (htlo : 1 ≤ t) (hthi : t ≤ 102*σ-76) :
    ((2)*(0)+(0))*t+((3-4*σ)*(1/2)+(2)*(2-2*σ)) ≤ energyClauseThreeSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (102*σ-76) t
    ((2)*(0)+(0)) ((3-4*σ)*(1/2)+(2)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(173/229))
      (by linarith : 0 ≤ (241/319)-σ)]

theorem energyClauseThree_low_3_1 {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (_hhi : σ ≤ 241/319)
    (htlo : 102*σ-76 ≤ t) (hthi : t ≤ 100*σ-372/5) :
    ((2)*(1)+(0))*t+((3-4*σ)*(1/2)+(2)*(78-104*σ)) ≤ energyClauseThreeSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (102*σ-76) (100*σ-372/5) t
    ((2)*(1)+(0)) ((3-4*σ)*(1/2)+(2)*(78-104*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(173/229))
      (by linarith : 0 ≤ (241/319)-σ)]

theorem energyClauseThree_low_3_2 {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 241/319)
    (htlo : 100*σ-372/5 ≤ t) (hthi : t ≤ 6/5) :
    ((2)*(0)+(0))*t+((3-4*σ)*(1/2)+(2)*(18/5-4*σ)) ≤ energyClauseThreeSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (100*σ-372/5) (6/5) t
    ((2)*(0)+(0)) ((3-4*σ)*(1/2)+(2)*(18/5-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(173/229))
      (by linarith : 0 ≤ (241/319)-σ)]

theorem energyClauseThree_low_4_0 {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 241/319)
    (htlo : 1 ≤ t) (hthi : t ≤ 102*σ-76) :
    ((3)*(0)+(0))*t+((1-2*σ)*(1/2)+(3)*(2-2*σ)) ≤ energyClauseThreeSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (102*σ-76) t
    ((3)*(0)+(0)) ((1-2*σ)*(1/2)+(3)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(173/229))
      (by linarith : 0 ≤ (241/319)-σ)]

theorem energyClauseThree_low_4_1 {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (_hhi : σ ≤ 241/319)
    (htlo : 102*σ-76 ≤ t) (hthi : t ≤ 100*σ-372/5) :
    ((3)*(1)+(0))*t+((1-2*σ)*(1/2)+(3)*(78-104*σ)) ≤ energyClauseThreeSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (102*σ-76) (100*σ-372/5) t
    ((3)*(1)+(0)) ((1-2*σ)*(1/2)+(3)*(78-104*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(173/229))
      (by linarith : 0 ≤ (241/319)-σ)]

theorem energyClauseThree_low_4_2 {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 241/319)
    (htlo : 100*σ-372/5 ≤ t) (hthi : t ≤ 6/5) :
    ((3)*(0)+(0))*t+((1-2*σ)*(1/2)+(3)*(18/5-4*σ)) ≤ energyClauseThreeSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (100*σ-372/5) (6/5) t
    ((3)*(0)+(0)) ((1-2*σ)*(1/2)+(3)*(18/5-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(173/229))
      (by linarith : 0 ≤ (241/319)-σ)]

theorem energyClauseThree_low_5_0 {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 241/319)
    (htlo : 1 ≤ t) (hthi : t ≤ 102*σ-76) :
    ((12/5)*(0)+(2/5))*t+(((8-16*σ)/5)*(1/2)+(12/5)*(2-2*σ)) ≤ energyClauseThreeSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (102*σ-76) t
    ((12/5)*(0)+(2/5)) (((8-16*σ)/5)*(1/2)+(12/5)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(173/229))
      (by linarith : 0 ≤ (241/319)-σ)]

theorem energyClauseThree_low_5_1 {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (_hhi : σ ≤ 241/319)
    (htlo : 102*σ-76 ≤ t) (hthi : t ≤ 100*σ-372/5) :
    ((12/5)*(1)+(2/5))*t+(((8-16*σ)/5)*(1/2)+(12/5)*(78-104*σ)) ≤ energyClauseThreeSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (102*σ-76) (100*σ-372/5) t
    ((12/5)*(1)+(2/5)) (((8-16*σ)/5)*(1/2)+(12/5)*(78-104*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(173/229))
      (by linarith : 0 ≤ (241/319)-σ)]

theorem energyClauseThree_low_5_2 {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 241/319)
    (htlo : 100*σ-372/5 ≤ t) (hthi : t ≤ 6/5) :
    ((12/5)*(0)+(2/5))*t+(((8-16*σ)/5)*(1/2)+(12/5)*(18/5-4*σ)) ≤ energyClauseThreeSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (100*σ-372/5) (6/5) t
    ((12/5)*(0)+(2/5)) (((8-16*σ)/5)*(1/2)+(12/5)*(18/5-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(173/229))
      (by linarith : 0 ≤ (241/319)-σ)]

theorem energyClauseThree_low_6_0 {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 241/319)
    (htlo : 1 ≤ t) (hthi : t ≤ 102*σ-76) :
    ((5/4)*(0)+(1/2))*t+((3-4*σ)*(1/2)+(5/4)*(2-2*σ)) ≤ energyClauseThreeSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (102*σ-76) t
    ((5/4)*(0)+(1/2)) ((3-4*σ)*(1/2)+(5/4)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(173/229))
      (by linarith : 0 ≤ (241/319)-σ)]

theorem energyClauseThree_low_6_1 {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (_hhi : σ ≤ 241/319)
    (htlo : 102*σ-76 ≤ t) (hthi : t ≤ 100*σ-372/5) :
    ((5/4)*(1)+(1/2))*t+((3-4*σ)*(1/2)+(5/4)*(78-104*σ)) ≤ energyClauseThreeSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (102*σ-76) (100*σ-372/5) t
    ((5/4)*(1)+(1/2)) ((3-4*σ)*(1/2)+(5/4)*(78-104*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(173/229))
      (by linarith : 0 ≤ (241/319)-σ)]

theorem energyClauseThree_low_6_2 {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 241/319)
    (htlo : 100*σ-372/5 ≤ t) (hthi : t ≤ 6/5) :
    ((5/4)*(0)+(1/2))*t+((3-4*σ)*(1/2)+(5/4)*(18/5-4*σ)) ≤ energyClauseThreeSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (100*σ-372/5) (6/5) t
    ((5/4)*(0)+(1/2)) ((3-4*σ)*(1/2)+(5/4)*(18/5-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(173/229))
      (by linarith : 0 ≤ (241/319)-σ)]

theorem energyClauseThree_low_7_0 {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 241/319)
    (htlo : 1 ≤ t) (hthi : t ≤ 102*σ-76) :
    ((21/8)*(0)+(1/4))*t+((1-2*σ)*(1/2)+(21/8)*(2-2*σ)) ≤ energyClauseThreeFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (102*σ-76) t
    ((21/8)*(0)+(1/4)) ((1-2*σ)*(1/2)+(21/8)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(173/229))
      (by linarith : 0 ≤ (241/319)-σ)]

theorem energyClauseThree_low_7_1 {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 241/319)
    (htlo : 102*σ-76 ≤ t) (hthi : t ≤ 100*σ-372/5) :
    ((21/8)*(1)+(1/4))*t+((1-2*σ)*(1/2)+(21/8)*(78-104*σ)) ≤ energyClauseThreeFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (102*σ-76) (100*σ-372/5) t
    ((21/8)*(1)+(1/4)) ((1-2*σ)*(1/2)+(21/8)*(78-104*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(173/229))
      (by linarith : 0 ≤ (241/319)-σ)]

theorem energyClauseThree_low_7_2 {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 241/319)
    (htlo : 100*σ-372/5 ≤ t) (hthi : t ≤ 6/5) :
    ((21/8)*(0)+(1/4))*t+((1-2*σ)*(1/2)+(21/8)*(18/5-4*σ)) ≤ energyClauseThreeFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (100*σ-372/5) (6/5) t
    ((21/8)*(0)+(1/4)) ((1-2*σ)*(1/2)+(21/8)*(18/5-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(173/229))
      (by linarith : 0 ≤ (241/319)-σ)]

theorem energyClauseThree_low_8_0 {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 241/319)
    (htlo : 1 ≤ t) (hthi : t ≤ 102*σ-76) :
    ((9/5)*(0)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(2-2*σ)) ≤ energyClauseThreeSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (102*σ-76) t
    ((9/5)*(0)+(4/5)) (((8-16*σ)/5)*(1/2)+(9/5)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(173/229))
      (by linarith : 0 ≤ (241/319)-σ)]

theorem energyClauseThree_low_8_1 {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 241/319)
    (htlo : 102*σ-76 ≤ t) (hthi : t ≤ 100*σ-372/5) :
    ((9/5)*(1)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(78-104*σ)) ≤ energyClauseThreeSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (102*σ-76) (100*σ-372/5) t
    ((9/5)*(1)+(4/5)) (((8-16*σ)/5)*(1/2)+(9/5)*(78-104*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(173/229))
      (by linarith : 0 ≤ (241/319)-σ)]

theorem energyClauseThree_low_8_2 {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 241/319)
    (htlo : 100*σ-372/5 ≤ t) (hthi : t ≤ 6/5) :
    ((9/5)*(0)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(18/5-4*σ)) ≤ energyClauseThreeSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (100*σ-372/5) (6/5) t
    ((9/5)*(0)+(4/5)) (((8-16*σ)/5)*(1/2)+(9/5)*(18/5-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseThreeSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(173/229))
      (by linarith : 0 ≤ (241/319)-σ)]

end TaoTrudgianYang2025
