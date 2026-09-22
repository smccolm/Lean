import TaoTrudgianYang2025.EnergyClauseSixRates

/-!
# Middle and tall height certificates for Add-est (vi)

The independent q-powered witness covers both moving middle ranges.
The actual Guth--Maynard and companion cardinality caps cover the tall range.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem energyClauseSix_low_middle_0 {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 281/371)
    (htlo : 77*σ/2-28 ≤ t) (hthi : t ≤ 6/5) :
    (1)*t+(60-80*σ+4-4*σ) ≤ energyClauseSixFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (77*σ/2-28) (6/5) t
    (1) (60-80*σ+4-4*σ) _ htlo hthi
  all_goals
    unfold energyClauseSixFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(664/877))
      (by linarith : 0 ≤ (281/371)-σ)]

theorem energyClauseSix_low_middle_1 {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (_hhi : σ ≤ 281/371)
    (htlo : 77*σ/2-28 ≤ t) (hthi : t ≤ 6/5) :
    (5/2)*t+((3-4*σ+5*(60-80*σ))/2) ≤ energyClauseSixFirstRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (77*σ/2-28) (6/5) t
    (5/2) ((3-4*σ+5*(60-80*σ))/2) _ htlo hthi
  all_goals
    unfold energyClauseSixFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(664/877))
      (by linarith : 0 ≤ (281/371)-σ)]

theorem energyClauseSix_high_middle_0 {σ t : ℝ}
    (hlo : 281/371 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : (14*σ+1)/10 ≤ t) (hthi : t ≤ 6/5) :
    (1)*t+(19/5-(29/5)*σ+4-4*σ) ≤ energyClauseSixSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((14*σ+1)/10) (6/5) t
    (1) (19/5-(29/5)*σ+4-4*σ) _ htlo hthi
  all_goals
    unfold energyClauseSixSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(281/371))
      (by linarith : 0 ≤ (31/40)-σ)]

theorem energyClauseSix_high_middle_1 {σ t : ℝ}
    (hlo : 281/371 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : (14*σ+1)/10 ≤ t) (hthi : t ≤ 6/5) :
    (5/2)*t+((3-4*σ+5*(19/5-(29/5)*σ))/2) ≤ energyClauseSixSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints ((14*σ+1)/10) (6/5) t
    (5/2) ((3-4*σ+5*(19/5-(29/5)*σ))/2) _ htlo hthi
  all_goals
    unfold energyClauseSixSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(281/371))
      (by linarith : 0 ≤ (31/40)-σ)]

theorem energyClauseSix_tall_0_0 {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : 6/5 ≤ t) (hthi : t ≤ σ+3/5) :
    (1)*t+((12/5-4*σ)+4-4*σ) ≤ energyClauseSixSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (6/5) (σ+3/5) t
    (1) ((12/5-4*σ)+4-4*σ) _ htlo hthi
  all_goals
    unfold energyClauseSixSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(664/877))
      (by linarith : 0 ≤ (31/40)-σ)]

theorem energyClauseSix_tall_0_1 {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : σ+3/5 ≤ t) (hthi : t ≤ 3/2) :
    (0)*t+((3-3*σ)+4-4*σ) ≤ energyClauseSixSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (σ+3/5) (3/2) t
    (0) ((3-3*σ)+4-4*σ) _ htlo hthi
  all_goals
    unfold energyClauseSixSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(664/877))
      (by linarith : 0 ≤ (31/40)-σ)]

theorem energyClauseSix_tall_1_0 {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (_hhi : σ ≤ 31/40)
    (htlo : 6/5 ≤ t) (hthi : t ≤ σ+3/5) :
    ((5/2)*(1))*t+((3-4*σ+5*(12/5-4*σ))/2) ≤ energyClauseSixSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (6/5) (σ+3/5) t
    ((5/2)*(1)) ((3-4*σ+5*(12/5-4*σ))/2) _ htlo hthi
  all_goals
    unfold energyClauseSixSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(664/877))
      (by linarith : 0 ≤ (31/40)-σ)]

theorem energyClauseSix_tall_1_1 {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : σ+3/5 ≤ t) (hthi : t ≤ 3/2) :
    ((5/2)*(0))*t+((3-4*σ+5*(3-3*σ))/2) ≤ energyClauseSixSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (σ+3/5) (3/2) t
    ((5/2)*(0)) ((3-4*σ+5*(3-3*σ))/2) _ htlo hthi
  all_goals
    unfold energyClauseSixSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(664/877))
      (by linarith : 0 ≤ (31/40)-σ)]

end TaoTrudgianYang2025
