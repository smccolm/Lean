import TaoTrudgianYang2025.EnergyClauseSixRates

/-!
# Exact low-sigma short-height certificates for Add-est (vi)

All nine independent-power Heath--Brown branches are bounded on
the full blueprint sigma interval and both closed height pieces.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem energyClauseSix_low_0_0 {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 281/371)
    (htlo : 1 ≤ t) (hthi : t ≤ 78*σ-58) :
    ((1)*(0)+(0))*t+((4-4*σ)*(2/3)+(1)*(2-2*σ)) ≤ energyClauseSixFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (78*σ-58) t
    ((1)*(0)+(0)) ((4-4*σ)*(2/3)+(1)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSixFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(664/877))
      (by linarith : 0 ≤ (281/371)-σ)]

theorem energyClauseSix_low_0_1 {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 281/371)
    (htlo : 78*σ-58 ≤ t) (hthi : t ≤ 77*σ/2-28) :
    ((1)*(1)+(0))*t+((4-4*σ)*(2/3)+(1)*(60-80*σ)) ≤ energyClauseSixFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (78*σ-58) (77*σ/2-28) t
    ((1)*(1)+(0)) ((4-4*σ)*(2/3)+(1)*(60-80*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSixFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(664/877))
      (by linarith : 0 ≤ (281/371)-σ)]

theorem energyClauseSix_low_1_0 {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 281/371)
    (htlo : 1 ≤ t) (hthi : t ≤ 78*σ-58) :
    ((5/2)*(0)+(0))*t+(((3-4*σ)/2)*(1/2)+(5/2)*(2-2*σ)) ≤ energyClauseSixFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (78*σ-58) t
    ((5/2)*(0)+(0)) (((3-4*σ)/2)*(1/2)+(5/2)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSixFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(664/877))
      (by linarith : 0 ≤ (281/371)-σ)]

theorem energyClauseSix_low_1_1 {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 281/371)
    (htlo : 78*σ-58 ≤ t) (hthi : t ≤ 77*σ/2-28) :
    ((5/2)*(1)+(0))*t+(((3-4*σ)/2)*(1/2)+(5/2)*(60-80*σ)) ≤ energyClauseSixFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (78*σ-58) (77*σ/2-28) t
    ((5/2)*(1)+(0)) (((3-4*σ)/2)*(1/2)+(5/2)*(60-80*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSixFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(664/877))
      (by linarith : 0 ≤ (281/371)-σ)]

theorem energyClauseSix_low_2_0 {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 281/371)
    (htlo : 1 ≤ t) (hthi : t ≤ 78*σ-58) :
    ((8/5)*(0)+(2/5))*t+(((12-16*σ)/5)*(1/2)+(8/5)*(2-2*σ)) ≤ energyClauseSixFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (78*σ-58) t
    ((8/5)*(0)+(2/5)) (((12-16*σ)/5)*(1/2)+(8/5)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSixFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(664/877))
      (by linarith : 0 ≤ (281/371)-σ)]

theorem energyClauseSix_low_2_1 {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 281/371)
    (htlo : 78*σ-58 ≤ t) (hthi : t ≤ 77*σ/2-28) :
    ((8/5)*(1)+(2/5))*t+(((12-16*σ)/5)*(1/2)+(8/5)*(60-80*σ)) ≤ energyClauseSixFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (78*σ-58) (77*σ/2-28) t
    ((8/5)*(1)+(2/5)) (((12-16*σ)/5)*(1/2)+(8/5)*(60-80*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSixFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(664/877))
      (by linarith : 0 ≤ (281/371)-σ)]

theorem energyClauseSix_low_3_0 {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 281/371)
    (htlo : 1 ≤ t) (hthi : t ≤ 78*σ-58) :
    ((2)*(0)+(0))*t+((3-4*σ)*(1/2)+(2)*(2-2*σ)) ≤ energyClauseSixFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (78*σ-58) t
    ((2)*(0)+(0)) ((3-4*σ)*(1/2)+(2)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSixFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(664/877))
      (by linarith : 0 ≤ (281/371)-σ)]

theorem energyClauseSix_low_3_1 {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 281/371)
    (htlo : 78*σ-58 ≤ t) (hthi : t ≤ 77*σ/2-28) :
    ((2)*(1)+(0))*t+((3-4*σ)*(1/2)+(2)*(60-80*σ)) ≤ energyClauseSixFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (78*σ-58) (77*σ/2-28) t
    ((2)*(1)+(0)) ((3-4*σ)*(1/2)+(2)*(60-80*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSixFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(664/877))
      (by linarith : 0 ≤ (281/371)-σ)]

theorem energyClauseSix_low_4_0 {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 281/371)
    (htlo : 1 ≤ t) (hthi : t ≤ 78*σ-58) :
    ((3)*(0)+(0))*t+((1-2*σ)*(1/2)+(3)*(2-2*σ)) ≤ energyClauseSixFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (78*σ-58) t
    ((3)*(0)+(0)) ((1-2*σ)*(1/2)+(3)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSixFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(664/877))
      (by linarith : 0 ≤ (281/371)-σ)]

theorem energyClauseSix_low_4_1 {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 281/371)
    (htlo : 78*σ-58 ≤ t) (hthi : t ≤ 77*σ/2-28) :
    ((3)*(1)+(0))*t+((1-2*σ)*(1/2)+(3)*(60-80*σ)) ≤ energyClauseSixFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (78*σ-58) (77*σ/2-28) t
    ((3)*(1)+(0)) ((1-2*σ)*(1/2)+(3)*(60-80*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSixFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(664/877))
      (by linarith : 0 ≤ (281/371)-σ)]

theorem energyClauseSix_low_5_0 {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 281/371)
    (htlo : 1 ≤ t) (hthi : t ≤ 78*σ-58) :
    ((12/5)*(0)+(2/5))*t+(((8-16*σ)/5)*(1/2)+(12/5)*(2-2*σ)) ≤ energyClauseSixFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (78*σ-58) t
    ((12/5)*(0)+(2/5)) (((8-16*σ)/5)*(1/2)+(12/5)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSixFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(664/877))
      (by linarith : 0 ≤ (281/371)-σ)]

theorem energyClauseSix_low_5_1 {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 281/371)
    (htlo : 78*σ-58 ≤ t) (hthi : t ≤ 77*σ/2-28) :
    ((12/5)*(1)+(2/5))*t+(((8-16*σ)/5)*(1/2)+(12/5)*(60-80*σ)) ≤ energyClauseSixFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (78*σ-58) (77*σ/2-28) t
    ((12/5)*(1)+(2/5)) (((8-16*σ)/5)*(1/2)+(12/5)*(60-80*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSixFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(664/877))
      (by linarith : 0 ≤ (281/371)-σ)]

theorem energyClauseSix_low_6_0 {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 281/371)
    (htlo : 1 ≤ t) (hthi : t ≤ 78*σ-58) :
    ((5/4)*(0)+(1/2))*t+((3-4*σ)*(1/2)+(5/4)*(2-2*σ)) ≤ energyClauseSixFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (78*σ-58) t
    ((5/4)*(0)+(1/2)) ((3-4*σ)*(1/2)+(5/4)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSixFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(664/877))
      (by linarith : 0 ≤ (281/371)-σ)]

theorem energyClauseSix_low_6_1 {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 281/371)
    (htlo : 78*σ-58 ≤ t) (hthi : t ≤ 77*σ/2-28) :
    ((5/4)*(1)+(1/2))*t+((3-4*σ)*(1/2)+(5/4)*(60-80*σ)) ≤ energyClauseSixFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (78*σ-58) (77*σ/2-28) t
    ((5/4)*(1)+(1/2)) ((3-4*σ)*(1/2)+(5/4)*(60-80*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSixFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(664/877))
      (by linarith : 0 ≤ (281/371)-σ)]

theorem energyClauseSix_low_7_0 {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 281/371)
    (htlo : 1 ≤ t) (hthi : t ≤ 78*σ-58) :
    ((21/8)*(0)+(1/4))*t+((1-2*σ)*(1/2)+(21/8)*(2-2*σ)) ≤ energyClauseSixFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (78*σ-58) t
    ((21/8)*(0)+(1/4)) ((1-2*σ)*(1/2)+(21/8)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSixFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(664/877))
      (by linarith : 0 ≤ (281/371)-σ)]

theorem energyClauseSix_low_7_1 {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 281/371)
    (htlo : 78*σ-58 ≤ t) (hthi : t ≤ 77*σ/2-28) :
    ((21/8)*(1)+(1/4))*t+((1-2*σ)*(1/2)+(21/8)*(60-80*σ)) ≤ energyClauseSixFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (78*σ-58) (77*σ/2-28) t
    ((21/8)*(1)+(1/4)) ((1-2*σ)*(1/2)+(21/8)*(60-80*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSixFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(664/877))
      (by linarith : 0 ≤ (281/371)-σ)]

theorem energyClauseSix_low_8_0 {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 281/371)
    (htlo : 1 ≤ t) (hthi : t ≤ 78*σ-58) :
    ((9/5)*(0)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(2-2*σ)) ≤ energyClauseSixFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (1) (78*σ-58) t
    ((9/5)*(0)+(4/5)) (((8-16*σ)/5)*(1/2)+(9/5)*(2-2*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSixFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(664/877))
      (by linarith : 0 ≤ (281/371)-σ)]

theorem energyClauseSix_low_8_1 {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 281/371)
    (htlo : 78*σ-58 ≤ t) (hthi : t ≤ 77*σ/2-28) :
    ((9/5)*(1)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(60-80*σ)) ≤ energyClauseSixFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (78*σ-58) (77*σ/2-28) t
    ((9/5)*(1)+(4/5)) (((8-16*σ)/5)*(1/2)+(9/5)*(60-80*σ)) _ htlo hthi
  all_goals
    unfold energyClauseSixFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(664/877))
      (by linarith : 0 ≤ (281/371)-σ)]

end TaoTrudgianYang2025
