import TaoTrudgianYang2025.HeathBrownNineBranches

/-!
# Exact affine certificates for Add-est (ii)

Every inequality is proved over its whole real parameter interval.
Endpoint reduction is exact; the remaining quadratic inequalities are
checked by Lean arithmetic, not by sampled or external solver evidence.
-/

noncomputable section

namespace TaoTrudgianYang2025

def energyClauseTwoFirstRate (σ : ℝ) : ℝ := 5*(18-19*σ)/(2*(5*σ+3))
def energyClauseTwoSecondRate (σ : ℝ) : ℝ := 2*(45-44*σ)/(2*σ+15)
def energyClauseTwoRate (σ : ℝ) : ℝ :=
  max (energyClauseTwoFirstRate σ) (energyClauseTwoSecondRate σ)

theorem energy_affine_le_mul_of_endpoints
    (a b t u v B : ℝ) (hat : a ≤ t) (htb : t ≤ b)
    (ha : u*a+v ≤ B*a) (hb : u*b+v ≤ B*b) :
    u*t+v ≤ B*t := by
  by_cases hu : u ≤ B
  · nlinarith [mul_nonneg (sub_nonneg.mpr hat) (sub_nonneg.mpr hu)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr htb) (sub_nonneg.mpr (le_of_not_ge hu))]

theorem energyClauseTwoRate_pos {σ : ℝ} (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4) :
    0 < energyClauseTwoRate σ := by
  apply lt_of_lt_of_le _ (le_max_left _ _)
  exact div_pos (by linarith : 0 < 5*(18-19*σ)) (by linarith)

theorem energyClauseTwo_high_linear_first {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 6/5 ≤ t) (hthi : t ≤ σ+3/5) :
    (1)*t+((12/5-4*σ)+4-4*σ) ≤ energyClauseTwoFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (6/5) (σ+3/5) t (1) ((12/5-4*σ)+4-4*σ) _
    htlo hthi
  all_goals
    unfold energyClauseTwoFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(7/10))
      (by linarith : 0 ≤ (3/4)-σ)]

theorem energyClauseTwo_high_linear_second {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (_hhi : σ ≤ 3/4)
    (htlo : 6/5 ≤ t) (hthi : t ≤ σ+3/5) :
    (5/2*(1))*t+((3-4*σ+5*(12/5-4*σ))/2) ≤ energyClauseTwoFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (6/5) (σ+3/5) t (5/2*(1)) ((3-4*σ+5*(12/5-4*σ))/2) _
    htlo hthi
  all_goals
    unfold energyClauseTwoFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(7/10))
      (by linarith : 0 ≤ (3/4)-σ)]

theorem energyClauseTwo_high_constant_first {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : σ+3/5 ≤ t) (hthi : t ≤ 3/2) :
    (0)*t+((3-3*σ)+4-4*σ) ≤ energyClauseTwoFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (σ+3/5) (3/2) t (0) ((3-3*σ)+4-4*σ) _
    htlo hthi
  all_goals
    unfold energyClauseTwoFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(7/10))
      (by linarith : 0 ≤ (3/4)-σ)]

theorem energyClauseTwo_high_constant_second {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : σ+3/5 ≤ t) (hthi : t ≤ 3/2) :
    (5/2*(0))*t+((3-4*σ+5*(3-3*σ))/2) ≤ energyClauseTwoFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (σ+3/5) (3/2) t (5/2*(0)) ((3-4*σ+5*(3-3*σ))/2) _
    htlo hthi
  all_goals
    unfold energyClauseTwoFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(7/10))
      (by linarith : 0 ≤ (3/4)-σ)]

theorem energyClauseTwo_low_linear_second {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 1 ≤ t) (hthi : t ≤ 13/5-2*σ) :
    (5/2*(1))*t+((3-4*σ+5*(1-2*σ))/2) ≤ energyClauseTwoFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (13/5-2*σ) t (5/2*(1)) ((3-4*σ+5*(1-2*σ))/2) _
    htlo hthi
  all_goals
    unfold energyClauseTwoFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(7/10))
      (by linarith : 0 ≤ (3/4)-σ)]

theorem energyClauseTwo_low_constant_second {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 13/5-2*σ ≤ t) (hthi : t ≤ 6/5) :
    (5/2*(0))*t+((3-4*σ+5*(18/5-4*σ))/2) ≤ energyClauseTwoFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (13/5-2*σ) (6/5) t (5/2*(0)) ((3-4*σ+5*(18/5-4*σ))/2) _
    htlo hthi
  all_goals
    unfold energyClauseTwoFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(7/10))
      (by linarith : 0 ≤ (3/4)-σ)]

theorem energyClauseTwo_secondary_0_low_linear {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 1 ≤ t) (hthi : t ≤ 13/5-2*σ) :
    ((1)*(1)+(0))*t+((4-4*σ)*(2/3)+(1)*(1-2*σ)) ≤ energyClauseTwoFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (13/5-2*σ) t ((1)*(1)+(0)) ((4-4*σ)*(2/3)+(1)*(1-2*σ)) _
    htlo hthi
  all_goals
    unfold energyClauseTwoFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(7/10))
      (by linarith : 0 ≤ (3/4)-σ)]

theorem energyClauseTwo_secondary_0_low_constant {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 13/5-2*σ ≤ t) (hthi : t ≤ 6/5) :
    ((1)*(0)+(0))*t+((4-4*σ)*(2/3)+(1)*(18/5-4*σ)) ≤ energyClauseTwoFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (13/5-2*σ) (6/5) t ((1)*(0)+(0)) ((4-4*σ)*(2/3)+(1)*(18/5-4*σ)) _
    htlo hthi
  all_goals
    unfold energyClauseTwoFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(7/10))
      (by linarith : 0 ≤ (3/4)-σ)]

theorem energyClauseTwo_secondary_1_low_linear {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 1 ≤ t) (hthi : t ≤ 13/5-2*σ) :
    ((5/2)*(1)+(0))*t+(((3-4*σ)/2)*(2/3)+(5/2)*(1-2*σ)) ≤ energyClauseTwoFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (13/5-2*σ) t ((5/2)*(1)+(0)) (((3-4*σ)/2)*(2/3)+(5/2)*(1-2*σ)) _
    htlo hthi
  all_goals
    unfold energyClauseTwoFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(7/10))
      (by linarith : 0 ≤ (3/4)-σ)]

theorem energyClauseTwo_secondary_1_low_constant {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 13/5-2*σ ≤ t) (hthi : t ≤ 6/5) :
    ((5/2)*(0)+(0))*t+(((3-4*σ)/2)*(2/3)+(5/2)*(18/5-4*σ)) ≤ energyClauseTwoFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (13/5-2*σ) (6/5) t ((5/2)*(0)+(0)) (((3-4*σ)/2)*(2/3)+(5/2)*(18/5-4*σ)) _
    htlo hthi
  all_goals
    unfold energyClauseTwoFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(7/10))
      (by linarith : 0 ≤ (3/4)-σ)]

theorem energyClauseTwo_secondary_2_low_linear {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 1 ≤ t) (hthi : t ≤ 13/5-2*σ) :
    ((8/5)*(1)+(2/5))*t+(((12-16*σ)/5)*(2/3)+(8/5)*(1-2*σ)) ≤ energyClauseTwoFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (13/5-2*σ) t ((8/5)*(1)+(2/5)) (((12-16*σ)/5)*(2/3)+(8/5)*(1-2*σ)) _
    htlo hthi
  all_goals
    unfold energyClauseTwoFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(7/10))
      (by linarith : 0 ≤ (3/4)-σ)]

theorem energyClauseTwo_secondary_2_low_constant {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 13/5-2*σ ≤ t) (hthi : t ≤ 6/5) :
    ((8/5)*(0)+(2/5))*t+(((12-16*σ)/5)*(2/3)+(8/5)*(18/5-4*σ)) ≤ energyClauseTwoFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (13/5-2*σ) (6/5) t ((8/5)*(0)+(2/5)) (((12-16*σ)/5)*(2/3)+(8/5)*(18/5-4*σ)) _
    htlo hthi
  all_goals
    unfold energyClauseTwoFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(7/10))
      (by linarith : 0 ≤ (3/4)-σ)]

theorem energyClauseTwo_secondary_3_low_linear {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 1 ≤ t) (hthi : t ≤ 13/5-2*σ) :
    ((2)*(1)+(0))*t+((3-4*σ)*(2/3)+(2)*(1-2*σ)) ≤ energyClauseTwoFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (13/5-2*σ) t ((2)*(1)+(0)) ((3-4*σ)*(2/3)+(2)*(1-2*σ)) _
    htlo hthi
  all_goals
    unfold energyClauseTwoFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(7/10))
      (by linarith : 0 ≤ (3/4)-σ)]

theorem energyClauseTwo_secondary_3_low_constant {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 13/5-2*σ ≤ t) (hthi : t ≤ 6/5) :
    ((2)*(0)+(0))*t+((3-4*σ)*(2/3)+(2)*(18/5-4*σ)) ≤ energyClauseTwoFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (13/5-2*σ) (6/5) t ((2)*(0)+(0)) ((3-4*σ)*(2/3)+(2)*(18/5-4*σ)) _
    htlo hthi
  all_goals
    unfold energyClauseTwoFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(7/10))
      (by linarith : 0 ≤ (3/4)-σ)]

theorem energyClauseTwo_secondary_5_low_linear {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 1 ≤ t) (hthi : t ≤ 13/5-2*σ) :
    ((12/5)*(1)+(2/5))*t+(((8-16*σ)/5)*(1/2)+(12/5)*(1-2*σ)) ≤ energyClauseTwoFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (13/5-2*σ) t ((12/5)*(1)+(2/5)) (((8-16*σ)/5)*(1/2)+(12/5)*(1-2*σ)) _
    htlo hthi
  all_goals
    unfold energyClauseTwoFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(7/10))
      (by linarith : 0 ≤ (3/4)-σ)]

theorem energyClauseTwo_secondary_5_low_constant {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 13/5-2*σ ≤ t) (hthi : t ≤ 6/5) :
    ((12/5)*(0)+(2/5))*t+(((8-16*σ)/5)*(1/2)+(12/5)*(18/5-4*σ)) ≤ energyClauseTwoFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (13/5-2*σ) (6/5) t ((12/5)*(0)+(2/5)) (((8-16*σ)/5)*(1/2)+(12/5)*(18/5-4*σ)) _
    htlo hthi
  all_goals
    unfold energyClauseTwoFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(7/10))
      (by linarith : 0 ≤ (3/4)-σ)]

theorem energyClauseTwo_secondary_6_low_linear {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 1 ≤ t) (hthi : t ≤ 13/5-2*σ) :
    ((5/4)*(1)+(1/2))*t+((3-4*σ)*(2/3)+(5/4)*(1-2*σ)) ≤ energyClauseTwoFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (13/5-2*σ) t ((5/4)*(1)+(1/2)) ((3-4*σ)*(2/3)+(5/4)*(1-2*σ)) _
    htlo hthi
  all_goals
    unfold energyClauseTwoFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(7/10))
      (by linarith : 0 ≤ (3/4)-σ)]

theorem energyClauseTwo_secondary_6_low_constant {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 13/5-2*σ ≤ t) (hthi : t ≤ 6/5) :
    ((5/4)*(0)+(1/2))*t+((3-4*σ)*(2/3)+(5/4)*(18/5-4*σ)) ≤ energyClauseTwoFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (13/5-2*σ) (6/5) t ((5/4)*(0)+(1/2)) ((3-4*σ)*(2/3)+(5/4)*(18/5-4*σ)) _
    htlo hthi
  all_goals
    unfold energyClauseTwoFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(7/10))
      (by linarith : 0 ≤ (3/4)-σ)]

theorem energyClauseTwo_secondary_8_low_linear_lower {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 29/40)
    (htlo : 1 ≤ t) (hthi : t ≤ 13/5-2*σ) :
    ((9/5)*(1)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(1-2*σ)) ≤ energyClauseTwoFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (13/5-2*σ) t ((9/5)*(1)+(4/5)) (((8-16*σ)/5)*(1/2)+(9/5)*(1-2*σ)) _
    htlo hthi
  all_goals
    unfold energyClauseTwoFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(7/10))
      (by linarith : 0 ≤ (29/40)-σ)]

theorem energyClauseTwo_secondary_8_low_linear_upper {σ t : ℝ}
    (hlo : 29/40 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 1 ≤ t) (hthi : t ≤ 13/5-2*σ) :
    ((9/5)*(1)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(1-2*σ)) ≤ energyClauseTwoSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (13/5-2*σ) t ((9/5)*(1)+(4/5)) (((8-16*σ)/5)*(1/2)+(9/5)*(1-2*σ)) _
    htlo hthi
  all_goals
    unfold energyClauseTwoSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(29/40))
      (by linarith : 0 ≤ (3/4)-σ)]

theorem energyClauseTwo_secondary_8_low_constant_lower {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 29/40)
    (htlo : 13/5-2*σ ≤ t) (hthi : t ≤ 6/5) :
    ((9/5)*(0)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(18/5-4*σ)) ≤ energyClauseTwoFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (13/5-2*σ) (6/5) t ((9/5)*(0)+(4/5)) (((8-16*σ)/5)*(1/2)+(9/5)*(18/5-4*σ)) _
    htlo hthi
  all_goals
    unfold energyClauseTwoFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(7/10))
      (by linarith : 0 ≤ (29/40)-σ)]

theorem energyClauseTwo_secondary_8_low_constant_upper {σ t : ℝ}
    (hlo : 29/40 ≤ σ) (_hhi : σ ≤ 3/4)
    (htlo : 13/5-2*σ ≤ t) (hthi : t ≤ 6/5) :
    ((9/5)*(0)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(18/5-4*σ)) ≤ energyClauseTwoSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (13/5-2*σ) (6/5) t ((9/5)*(0)+(4/5)) (((8-16*σ)/5)*(1/2)+(9/5)*(18/5-4*σ)) _
    htlo hthi
  all_goals
    unfold energyClauseTwoSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(29/40))
      (by linarith : 0 ≤ (3/4)-σ)]

theorem energyClauseTwo_trade_three_left {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 1 ≤ t) (hthi : t ≤ σ/2+3/4) :
    (3)*t+(7/2-7*σ) ≤ energyClauseTwoSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (σ/2+3/4) t (3) (7/2-7*σ) _
    htlo hthi
  all_goals
    unfold energyClauseTwoSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(7/10))
      (by linarith : 0 ≤ (3/4)-σ)]

theorem energyClauseTwo_trade_three_right {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : σ/2+3/4 ≤ t) (hthi : t ≤ 6/5) :
    (1)*t+(5-6*σ) ≤ energyClauseTwoSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (σ/2+3/4) (6/5) t (1) (5-6*σ) _
    htlo hthi
  all_goals
    unfold energyClauseTwoSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(7/10))
      (by linarith : 0 ≤ (3/4)-σ)]

theorem energyClauseTwo_trade_phase_left {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (_hhi : σ ≤ 3/4)
    (htlo : 1 ≤ t) (hthi : t ≤ 1+2*σ/15) :
    (23/8)*t+(25/8-25/4*σ) ≤ energyClauseTwoSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (1+2*σ/15) t (23/8) (25/8-25/4*σ) _
    htlo hthi
  all_goals
    unfold energyClauseTwoSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(7/10))
      (by linarith : 0 ≤ (3/4)-σ)]

theorem energyClauseTwo_trade_phase_right {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 1+2*σ/15 ≤ t) (hthi : t ≤ 6/5) :
    (1)*t+(5-6*σ) ≤ energyClauseTwoSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1+2*σ/15) (6/5) t (1) (5-6*σ) _
    htlo hthi
  all_goals
    unfold energyClauseTwoSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(7/10))
      (by linarith : 0 ≤ (3/4)-σ)]

end TaoTrudgianYang2025
