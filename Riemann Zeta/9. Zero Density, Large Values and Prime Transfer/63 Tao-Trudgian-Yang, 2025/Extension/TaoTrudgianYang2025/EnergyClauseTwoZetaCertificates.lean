import TaoTrudgianYang2025.EnergyClauseTwoCertificates

/-!
# Exact short-zeta certificates for Add-est (ii)

All nine Heath--Brown branches are checked on the whole source interval,
using the two genuine cardinality caps and their crossing at 4*sigma-1.
-/

noncomputable section
namespace TaoTrudgianYang2025

theorem energyClauseTwo_zeta_linear_0 {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 2*σ ≤ t) (hthi : t ≤ 4*σ-1) :
    ((1)*(2)+(0))*t+((4-4*σ)+(1)*(6-12*σ)) ≤ energyClauseTwoFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (2*σ) (4*σ-1) t ((1)*(2)+(0)) ((4-4*σ)+(1)*(6-12*σ)) _ htlo hthi
  all_goals
    unfold energyClauseTwoFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-7/10)
      (by linarith : 0 ≤ 3/4-σ)]

theorem energyClauseTwo_zeta_linear_1 {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 2*σ ≤ t) (hthi : t ≤ 4*σ-1) :
    ((5/2)*(2)+(0))*t+(((3-4*σ)/2)+(5/2)*(6-12*σ)) ≤ energyClauseTwoFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (2*σ) (4*σ-1) t ((5/2)*(2)+(0)) (((3-4*σ)/2)+(5/2)*(6-12*σ)) _ htlo hthi
  all_goals
    unfold energyClauseTwoFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-7/10)
      (by linarith : 0 ≤ 3/4-σ)]

theorem energyClauseTwo_zeta_linear_2 {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 2*σ ≤ t) (hthi : t ≤ 4*σ-1) :
    ((8/5)*(2)+(2/5))*t+(((12-16*σ)/5)+(8/5)*(6-12*σ)) ≤ energyClauseTwoFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (2*σ) (4*σ-1) t ((8/5)*(2)+(2/5)) (((12-16*σ)/5)+(8/5)*(6-12*σ)) _ htlo hthi
  all_goals
    unfold energyClauseTwoFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-7/10)
      (by linarith : 0 ≤ 3/4-σ)]

theorem energyClauseTwo_zeta_linear_3 {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 2*σ ≤ t) (hthi : t ≤ 4*σ-1) :
    ((2)*(2)+(0))*t+((3-4*σ)+(2)*(6-12*σ)) ≤ energyClauseTwoFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (2*σ) (4*σ-1) t ((2)*(2)+(0)) ((3-4*σ)+(2)*(6-12*σ)) _ htlo hthi
  all_goals
    unfold energyClauseTwoFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-7/10)
      (by linarith : 0 ≤ 3/4-σ)]

theorem energyClauseTwo_zeta_linear_4 {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 2*σ ≤ t) (hthi : t ≤ 4*σ-1) :
    ((3)*(2)+(0))*t+((1-2*σ)+(3)*(6-12*σ)) ≤ energyClauseTwoFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (2*σ) (4*σ-1) t ((3)*(2)+(0)) ((1-2*σ)+(3)*(6-12*σ)) _ htlo hthi
  all_goals
    unfold energyClauseTwoFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-7/10)
      (by linarith : 0 ≤ 3/4-σ)]

theorem energyClauseTwo_zeta_linear_5 {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 2*σ ≤ t) (hthi : t ≤ 4*σ-1) :
    ((12/5)*(2)+(2/5))*t+(((8-16*σ)/5)+(12/5)*(6-12*σ)) ≤ energyClauseTwoFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (2*σ) (4*σ-1) t ((12/5)*(2)+(2/5)) (((8-16*σ)/5)+(12/5)*(6-12*σ)) _ htlo hthi
  all_goals
    unfold energyClauseTwoFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-7/10)
      (by linarith : 0 ≤ 3/4-σ)]

theorem energyClauseTwo_zeta_linear_6 {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 2*σ ≤ t) (hthi : t ≤ 4*σ-1) :
    ((5/4)*(2)+(1/2))*t+((3-4*σ)+(5/4)*(6-12*σ)) ≤ energyClauseTwoFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (2*σ) (4*σ-1) t ((5/4)*(2)+(1/2)) ((3-4*σ)+(5/4)*(6-12*σ)) _ htlo hthi
  all_goals
    unfold energyClauseTwoFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-7/10)
      (by linarith : 0 ≤ 3/4-σ)]

theorem energyClauseTwo_zeta_linear_7 {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 2*σ ≤ t) (hthi : t ≤ 4*σ-1) :
    ((21/8)*(2)+(1/4))*t+((1-2*σ)+(21/8)*(6-12*σ)) ≤ energyClauseTwoFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (2*σ) (4*σ-1) t ((21/8)*(2)+(1/4)) ((1-2*σ)+(21/8)*(6-12*σ)) _ htlo hthi
  all_goals
    unfold energyClauseTwoFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-7/10)
      (by linarith : 0 ≤ 3/4-σ)]

theorem energyClauseTwo_zeta_linear_8 {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 2*σ ≤ t) (hthi : t ≤ 4*σ-1) :
    ((9/5)*(2)+(4/5))*t+(((8-16*σ)/5)+(9/5)*(6-12*σ)) ≤ energyClauseTwoFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (2*σ) (4*σ-1) t ((9/5)*(2)+(4/5)) (((8-16*σ)/5)+(9/5)*(6-12*σ)) _ htlo hthi
  all_goals
    unfold energyClauseTwoFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-7/10)
      (by linarith : 0 ≤ 3/4-σ)]

theorem energyClauseTwo_zeta_linear_branch {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 2*σ ≤ t) (hthi : t ≤ 4*σ-1) (i : Fin 9) :
    heathBrownNineBranch σ t ((2)*t+(6-12*σ)) 1 i ≤ energyClauseTwoFirstRate σ*t := by
  fin_cases i
  · change (4-4*σ)*1+((2)*t+(6-12*σ)) ≤ _
    have hc := energyClauseTwo_zeta_linear_0 hlo hhi htlo hthi
    linarith
  · change ((3-4*σ)*1+5*((2)*t+(6-12*σ)))/2 ≤ _
    have hc := energyClauseTwo_zeta_linear_1 hlo hhi htlo hthi
    linarith
  · change ((12-16*σ)*1+8*((2)*t+(6-12*σ))+2*t)/5 ≤ _
    have hc := energyClauseTwo_zeta_linear_2 hlo hhi htlo hthi
    linarith
  · change (3-4*σ)*1+2*((2)*t+(6-12*σ)) ≤ _
    have hc := energyClauseTwo_zeta_linear_3 hlo hhi htlo hthi
    linarith
  · change (1-2*σ)*1+3*((2)*t+(6-12*σ)) ≤ _
    have hc := energyClauseTwo_zeta_linear_4 hlo hhi htlo hthi
    linarith
  · change ((8-16*σ)*1+12*((2)*t+(6-12*σ))+2*t)/5 ≤ _
    have hc := energyClauseTwo_zeta_linear_5 hlo hhi htlo hthi
    linarith
  · change (3-4*σ)*1+5/4*((2)*t+(6-12*σ))+t/2 ≤ _
    have hc := energyClauseTwo_zeta_linear_6 hlo hhi htlo hthi
    linarith
  · change (1-2*σ)*1+21/8*((2)*t+(6-12*σ))+t/4 ≤ _
    have hc := energyClauseTwo_zeta_linear_7 hlo hhi htlo hthi
    linarith
  · change ((8-16*σ)*1+9*((2)*t+(6-12*σ))+4*t)/5 ≤ _
    have hc := energyClauseTwo_zeta_linear_8 hlo hhi htlo hthi
    linarith

theorem energyClauseTwo_zeta_constant_0 {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 4*σ-1 ≤ t) (hthi : t ≤ 2) :
    ((1)*(0)+(0))*t+((4-4*σ)+(1)*(4-4*σ)) ≤ energyClauseTwoFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (4*σ-1) (2) t ((1)*(0)+(0)) ((4-4*σ)+(1)*(4-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseTwoFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-7/10)
      (by linarith : 0 ≤ 3/4-σ)]

theorem energyClauseTwo_zeta_constant_1 {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 4*σ-1 ≤ t) (hthi : t ≤ 2) :
    ((5/2)*(0)+(0))*t+(((3-4*σ)/2)+(5/2)*(4-4*σ)) ≤ energyClauseTwoFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (4*σ-1) (2) t ((5/2)*(0)+(0)) (((3-4*σ)/2)+(5/2)*(4-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseTwoFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-7/10)
      (by linarith : 0 ≤ 3/4-σ)]

theorem energyClauseTwo_zeta_constant_2 {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 4*σ-1 ≤ t) (hthi : t ≤ 2) :
    ((8/5)*(0)+(2/5))*t+(((12-16*σ)/5)+(8/5)*(4-4*σ)) ≤ energyClauseTwoFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (4*σ-1) (2) t ((8/5)*(0)+(2/5)) (((12-16*σ)/5)+(8/5)*(4-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseTwoFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-7/10)
      (by linarith : 0 ≤ 3/4-σ)]

theorem energyClauseTwo_zeta_constant_3 {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 4*σ-1 ≤ t) (hthi : t ≤ 2) :
    ((2)*(0)+(0))*t+((3-4*σ)+(2)*(4-4*σ)) ≤ energyClauseTwoFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (4*σ-1) (2) t ((2)*(0)+(0)) ((3-4*σ)+(2)*(4-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseTwoFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-7/10)
      (by linarith : 0 ≤ 3/4-σ)]

theorem energyClauseTwo_zeta_constant_4 {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 4*σ-1 ≤ t) (hthi : t ≤ 2) :
    ((3)*(0)+(0))*t+((1-2*σ)+(3)*(4-4*σ)) ≤ energyClauseTwoFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (4*σ-1) (2) t ((3)*(0)+(0)) ((1-2*σ)+(3)*(4-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseTwoFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-7/10)
      (by linarith : 0 ≤ 3/4-σ)]

theorem energyClauseTwo_zeta_constant_5 {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 4*σ-1 ≤ t) (hthi : t ≤ 2) :
    ((12/5)*(0)+(2/5))*t+(((8-16*σ)/5)+(12/5)*(4-4*σ)) ≤ energyClauseTwoFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (4*σ-1) (2) t ((12/5)*(0)+(2/5)) (((8-16*σ)/5)+(12/5)*(4-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseTwoFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-7/10)
      (by linarith : 0 ≤ 3/4-σ)]

theorem energyClauseTwo_zeta_constant_6 {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 4*σ-1 ≤ t) (hthi : t ≤ 2) :
    ((5/4)*(0)+(1/2))*t+((3-4*σ)+(5/4)*(4-4*σ)) ≤ energyClauseTwoFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (4*σ-1) (2) t ((5/4)*(0)+(1/2)) ((3-4*σ)+(5/4)*(4-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseTwoFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-7/10)
      (by linarith : 0 ≤ 3/4-σ)]

theorem energyClauseTwo_zeta_constant_7 {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 4*σ-1 ≤ t) (hthi : t ≤ 2) :
    ((21/8)*(0)+(1/4))*t+((1-2*σ)+(21/8)*(4-4*σ)) ≤ energyClauseTwoFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (4*σ-1) (2) t ((21/8)*(0)+(1/4)) ((1-2*σ)+(21/8)*(4-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseTwoFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-7/10)
      (by linarith : 0 ≤ 3/4-σ)]

theorem energyClauseTwo_zeta_constant_8 {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 4*σ-1 ≤ t) (hthi : t ≤ 2) :
    ((9/5)*(0)+(4/5))*t+(((8-16*σ)/5)+(9/5)*(4-4*σ)) ≤ energyClauseTwoFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (4*σ-1) (2) t ((9/5)*(0)+(4/5)) (((8-16*σ)/5)+(9/5)*(4-4*σ)) _ htlo hthi
  all_goals
    unfold energyClauseTwoFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-7/10)
      (by linarith : 0 ≤ 3/4-σ)]

theorem energyClauseTwo_zeta_constant_branch {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 4*σ-1 ≤ t) (hthi : t ≤ 2) (i : Fin 9) :
    heathBrownNineBranch σ t ((0)*t+(4-4*σ)) 1 i ≤ energyClauseTwoFirstRate σ*t := by
  fin_cases i
  · change (4-4*σ)*1+((0)*t+(4-4*σ)) ≤ _
    have hc := energyClauseTwo_zeta_constant_0 hlo hhi htlo hthi
    linarith
  · change ((3-4*σ)*1+5*((0)*t+(4-4*σ)))/2 ≤ _
    have hc := energyClauseTwo_zeta_constant_1 hlo hhi htlo hthi
    linarith
  · change ((12-16*σ)*1+8*((0)*t+(4-4*σ))+2*t)/5 ≤ _
    have hc := energyClauseTwo_zeta_constant_2 hlo hhi htlo hthi
    linarith
  · change (3-4*σ)*1+2*((0)*t+(4-4*σ)) ≤ _
    have hc := energyClauseTwo_zeta_constant_3 hlo hhi htlo hthi
    linarith
  · change (1-2*σ)*1+3*((0)*t+(4-4*σ)) ≤ _
    have hc := energyClauseTwo_zeta_constant_4 hlo hhi htlo hthi
    linarith
  · change ((8-16*σ)*1+12*((0)*t+(4-4*σ))+2*t)/5 ≤ _
    have hc := energyClauseTwo_zeta_constant_5 hlo hhi htlo hthi
    linarith
  · change (3-4*σ)*1+5/4*((0)*t+(4-4*σ))+t/2 ≤ _
    have hc := energyClauseTwo_zeta_constant_6 hlo hhi htlo hthi
    linarith
  · change (1-2*σ)*1+21/8*((0)*t+(4-4*σ))+t/4 ≤ _
    have hc := energyClauseTwo_zeta_constant_7 hlo hhi htlo hthi
    linarith
  · change ((8-16*σ)*1+9*((0)*t+(4-4*σ))+4*t)/5 ≤ _
    have hc := energyClauseTwo_zeta_constant_8 hlo hhi htlo hthi
    linarith

theorem energyClauseTwo_zeta_branch {σ t r : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 2*σ ≤ t) (hthi : t ≤ 2)
    (hr : r ≤ 2*t+6-12*σ) (hcap : r ≤ 4-4*σ) (i : Fin 9) :
    heathBrownNineBranch σ t r 1 i ≤ energyClauseTwoRate σ*t := by
  have hA := mul_le_mul_of_nonneg_right
    (le_max_left (energyClauseTwoFirstRate σ) (energyClauseTwoSecondRate σ))
    (by linarith : 0 ≤ t)
  change energyClauseTwoFirstRate σ*t ≤ energyClauseTwoRate σ*t at hA
  apply le_trans _ hA
  by_cases ht : t ≤ 4*σ-1
  · apply (heathBrownNineBranch_mono_card σ t 1 i (show r ≤ 2*t+(6-12*σ) by linarith)).trans
    exact energyClauseTwo_zeta_linear_branch hlo hhi htlo ht i
  · have hc := energyClauseTwo_zeta_constant_branch hlo hhi (le_of_not_ge ht) hthi i
    simp only [zero_mul,zero_add] at hc
    exact (heathBrownNineBranch_mono_card σ t 1 i hcap).trans hc

end TaoTrudgianYang2025
