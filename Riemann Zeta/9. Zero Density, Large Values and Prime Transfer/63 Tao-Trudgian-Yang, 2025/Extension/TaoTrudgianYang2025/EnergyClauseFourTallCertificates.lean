import TaoTrudgianYang2025.EnergyClauseFourRates

/-!
# High-local-height certificates for Add-est (iv)

The two simplified Heath--Brown branches use the actual linear
Guth--Maynard cap and the companion Jutila cardinality cap.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem energyClauseFour_tall_0_0 {σ t : ℝ}
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : 6/5 ≤ t) (hthi : t ≤ σ+3/5) :
    (1)*t+((12/5-4*σ)+4-4*σ) ≤ energyClauseFourSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (6/5) (σ+3/5) t
    (1) ((12/5-4*σ)+4-4*σ) _ htlo hthi
  all_goals
    unfold energyClauseFourSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(443/586))
      (by linarith : 0 ≤ (373/493)-σ)]

theorem energyClauseFour_tall_0_1 {σ t : ℝ}
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : σ+3/5 ≤ t) (hthi : t ≤ 3/2) :
    (0)*t+((3-3*σ)+4-4*σ) ≤ energyClauseFourSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (σ+3/5) (3/2) t
    (0) ((3-3*σ)+4-4*σ) _ htlo hthi
  all_goals
    unfold energyClauseFourSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(443/586))
      (by linarith : 0 ≤ (373/493)-σ)]

theorem energyClauseFour_tall_1_0 {σ t : ℝ}
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : 6/5 ≤ t) (hthi : t ≤ σ+3/5) :
    ((5/2)*(1))*t+((3-4*σ+5*(12/5-4*σ))/2) ≤ energyClauseFourSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (6/5) (σ+3/5) t
    ((5/2)*(1)) ((3-4*σ+5*(12/5-4*σ))/2) _ htlo hthi
  all_goals
    unfold energyClauseFourSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(443/586))
      (by linarith : 0 ≤ (373/493)-σ)]

theorem energyClauseFour_tall_1_1 {σ t : ℝ}
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : σ+3/5 ≤ t) (hthi : t ≤ 3/2) :
    ((5/2)*(0))*t+((3-4*σ+5*(3-3*σ))/2) ≤ energyClauseFourSecondRate σ*t := by
  apply energy_affine_le_mul_of_endpoints (σ+3/5) (3/2) t
    ((5/2)*(0)) ((3-4*σ+5*(3-3*σ))/2) _ htlo hthi
  all_goals
    unfold energyClauseFourSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(443/586))
      (by linarith : 0 ≤ (373/493)-σ)]

end TaoTrudgianYang2025
