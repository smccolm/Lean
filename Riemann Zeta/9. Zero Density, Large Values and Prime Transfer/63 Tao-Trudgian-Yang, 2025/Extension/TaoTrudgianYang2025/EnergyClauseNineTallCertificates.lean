import TaoTrudgianYang2025.EnergyClauseNineRates

/-! Exact closed-interval certificates for Add-est (ix).
Every displayed rational inequality is checked by the Lean kernel. -/

noncomputable section

namespace TaoTrudgianYang2025

theorem energyClauseNine_tall_0 {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 6*σ-3) :
    0*t+(7+-7*σ) ≤ energyClauseNineSecondRate σ*t := by
  have ha : 0*(3/2)+(7+-7*σ) ≤ energyClauseNineSecondRate σ*(3/2) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  have hb : 0*(6*σ-3)+(7+-7*σ) ≤ energyClauseNineSecondRate σ*(6*σ-3) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  exact energy_affine_le_mul_of_endpoints (3/2) (6*σ-3) t
    0 (7+-7*σ) (energyClauseNineSecondRate σ) htlo hthi ha hb

theorem energyClauseNine_tall_1 {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 6*σ-3) :
    0*t+(9+(-19/2)*σ) ≤ energyClauseNineSecondRate σ*t := by
  have ha : 0*(3/2)+(9+(-19/2)*σ) ≤ energyClauseNineSecondRate σ*(3/2) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  have hb : 0*(6*σ-3)+(9+(-19/2)*σ) ≤ energyClauseNineSecondRate σ*(6*σ-3) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  exact energy_affine_le_mul_of_endpoints (3/2) (6*σ-3) t
    0 (9+(-19/2)*σ) (energyClauseNineSecondRate σ) htlo hthi ha hb

theorem energyClauseNine_tall_2 {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 6*σ-3) :
    (2/5)*t+((36/5)+-8*σ) ≤ energyClauseNineSecondRate σ*t := by
  have ha : (2/5)*(3/2)+((36/5)+-8*σ) ≤ energyClauseNineSecondRate σ*(3/2) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  have hb : (2/5)*(6*σ-3)+((36/5)+-8*σ) ≤ energyClauseNineSecondRate σ*(6*σ-3) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  exact energy_affine_le_mul_of_endpoints (3/2) (6*σ-3) t
    (2/5) ((36/5)+-8*σ) (energyClauseNineSecondRate σ) htlo hthi ha hb

theorem energyClauseNine_tall_3 {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 6*σ-3) :
    (1/2)*t+((27/4)+(-31/4)*σ) ≤ energyClauseNineSecondRate σ*t := by
  have ha : (1/2)*(3/2)+((27/4)+(-31/4)*σ) ≤ energyClauseNineSecondRate σ*(3/2) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  have hb : (1/2)*(6*σ-3)+((27/4)+(-31/4)*σ) ≤ energyClauseNineSecondRate σ*(6*σ-3) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  exact energy_affine_le_mul_of_endpoints (3/2) (6*σ-3) t
    (1/2) ((27/4)+(-31/4)*σ) (energyClauseNineSecondRate σ) htlo hthi ha hb

theorem energyClauseNine_tall_4 {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 6*σ-3) :
    (1/4)*t+((71/8)+(-79/8)*σ) ≤ energyClauseNineSecondRate σ*t := by
  have ha : (1/4)*(3/2)+((71/8)+(-79/8)*σ) ≤ energyClauseNineSecondRate σ*(3/2) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  have hb : (1/4)*(6*σ-3)+((71/8)+(-79/8)*σ) ≤ energyClauseNineSecondRate σ*(6*σ-3) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  exact energy_affine_le_mul_of_endpoints (3/2) (6*σ-3) t
    (1/4) ((71/8)+(-79/8)*σ) (energyClauseNineSecondRate σ) htlo hthi ha hb

theorem energyClauseNine_tall_5 {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 6*σ-3) :
    (4/5)*t+(7+(-43/5)*σ) ≤ energyClauseNineSecondRate σ*t := by
  have ha : (4/5)*(3/2)+(7+(-43/5)*σ) ≤ energyClauseNineSecondRate σ*(3/2) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  have hb : (4/5)*(6*σ-3)+(7+(-43/5)*σ) ≤ energyClauseNineSecondRate σ*(6*σ-3) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  exact energy_affine_le_mul_of_endpoints (3/2) (6*σ-3) t
    (4/5) (7+(-43/5)*σ) (energyClauseNineSecondRate σ) htlo hthi ha hb

theorem energyClauseNine_cap_0 {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5) (htlo : (27*σ-18)/2 ≤ t) :
    7-7*σ ≤ energyClauseNineFirstRate σ*t := by
  have ha : 7-7*σ ≤ energyClauseNineFirstRate σ*((27*σ-18)/2) := by
    unfold energyClauseNineFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 9*(3*σ-2))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-84/109)
      (by linarith : 0 ≤ 4/5-σ), sq_nonneg (σ-84/109), sq_nonneg (4/5-σ)]
  have hpos : 0 ≤ energyClauseNineFirstRate σ := by
    unfold energyClauseNineFirstRate
    exact div_nonneg (by linarith) (by linarith)
  exact ha.trans (mul_le_mul_of_nonneg_left htlo hpos)

theorem energyClauseNine_cap_1 {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5) (htlo : (27*σ-18)/2 ≤ t) :
    9-(19/2)*σ ≤ energyClauseNineFirstRate σ*t := by
  have ha : 9-(19/2)*σ ≤ energyClauseNineFirstRate σ*((27*σ-18)/2) := by
    unfold energyClauseNineFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 9*(3*σ-2))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-84/109)
      (by linarith : 0 ≤ 4/5-σ), sq_nonneg (σ-84/109), sq_nonneg (4/5-σ)]
  have hpos : 0 ≤ energyClauseNineFirstRate σ := by
    unfold energyClauseNineFirstRate
    exact div_nonneg (by linarith) (by linarith)
  exact ha.trans (mul_le_mul_of_nonneg_left htlo hpos)

theorem energyClauseNine_cap_mixed_0 {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5) (htlo : (16*σ-8)/3 ≤ t) :
    7-7*σ ≤ energyClauseNineSecondRate σ*t := by
  have ha : 7-7*σ ≤ energyClauseNineSecondRate σ*((16*σ-8)/3) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-84/109)
      (by linarith : 0 ≤ 4/5-σ), sq_nonneg (σ-84/109), sq_nonneg (4/5-σ)]
  have hpos : 0 ≤ energyClauseNineSecondRate σ := by
    unfold energyClauseNineSecondRate
    exact div_nonneg (by linarith) (by linarith)
  exact ha.trans (mul_le_mul_of_nonneg_left htlo hpos)

theorem energyClauseNine_cap_mixed_1 {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5) (htlo : (16*σ-8)/3 ≤ t) :
    9-(19/2)*σ ≤ energyClauseNineSecondRate σ*t := by
  have ha : 9-(19/2)*σ ≤ energyClauseNineSecondRate σ*((16*σ-8)/3) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-84/109)
      (by linarith : 0 ≤ 4/5-σ), sq_nonneg (σ-84/109), sq_nonneg (4/5-σ)]
  have hpos : 0 ≤ energyClauseNineSecondRate σ := by
    unfold energyClauseNineSecondRate
    exact div_nonneg (by linarith) (by linarith)
  exact ha.trans (mul_le_mul_of_nonneg_left htlo hpos)

end TaoTrudgianYang2025
