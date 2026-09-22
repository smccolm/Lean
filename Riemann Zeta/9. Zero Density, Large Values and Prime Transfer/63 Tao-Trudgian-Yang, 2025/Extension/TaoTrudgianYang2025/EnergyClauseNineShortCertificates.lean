import TaoTrudgianYang2025.EnergyClauseNineRates

/-! Exact closed-interval certificates for Add-est (ix).
Every displayed rational inequality is checked by the Lean kernel. -/

noncomputable section

namespace TaoTrudgianYang2025

theorem energyClauseNine_short_diag_0 {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 4*σ-2 ≤ t) (hthi : t ≤ 6/5) :
    0*t+((14/3)+(-14/3)*σ) ≤ energyClauseNineSecondRate σ*t := by
  have ha : 0*(4*σ-2)+((14/3)+(-14/3)*σ) ≤ energyClauseNineSecondRate σ*(4*σ-2) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  have hb : 0*(6/5)+((14/3)+(-14/3)*σ) ≤ energyClauseNineSecondRate σ*(6/5) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  exact energy_affine_le_mul_of_endpoints (4*σ-2) (6/5) t
    0 ((14/3)+(-14/3)*σ) (energyClauseNineSecondRate σ) htlo hthi ha hb

theorem energyClauseNine_short_diag_1 {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 4*σ-2 ≤ t) (hthi : t ≤ 6/5) :
    0*t+((23/4)+-6*σ) ≤ energyClauseNineSecondRate σ*t := by
  have ha : 0*(4*σ-2)+((23/4)+-6*σ) ≤ energyClauseNineSecondRate σ*(4*σ-2) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  have hb : 0*(6/5)+((23/4)+-6*σ) ≤ energyClauseNineSecondRate σ*(6/5) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  exact energy_affine_le_mul_of_endpoints (4*σ-2) (6/5) t
    0 ((23/4)+-6*σ) (energyClauseNineSecondRate σ) htlo hthi ha hb

theorem energyClauseNine_short_diag_2 {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 4*σ-2 ≤ t) (hthi : t ≤ 6/5) :
    (2/5)*t+((22/5)+(-24/5)*σ) ≤ energyClauseNineSecondRate σ*t := by
  have ha : (2/5)*(4*σ-2)+((22/5)+(-24/5)*σ) ≤ energyClauseNineSecondRate σ*(4*σ-2) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  have hb : (2/5)*(6/5)+((22/5)+(-24/5)*σ) ≤ energyClauseNineSecondRate σ*(6/5) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  exact energy_affine_le_mul_of_endpoints (4*σ-2) (6/5) t
    (2/5) ((22/5)+(-24/5)*σ) (energyClauseNineSecondRate σ) htlo hthi ha hb

theorem energyClauseNine_short_diag_3 {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 4*σ-2 ≤ t) (hthi : t ≤ 6/5) :
    0*t+((11/2)+-6*σ) ≤ energyClauseNineSecondRate σ*t := by
  have ha : 0*(4*σ-2)+((11/2)+-6*σ) ≤ energyClauseNineSecondRate σ*(4*σ-2) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  have hb : 0*(6/5)+((11/2)+-6*σ) ≤ energyClauseNineSecondRate σ*(6/5) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  exact energy_affine_le_mul_of_endpoints (4*σ-2) (6/5) t
    0 ((11/2)+-6*σ) (energyClauseNineSecondRate σ) htlo hthi ha hb

theorem energyClauseNine_short_diag_4 {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 4*σ-2 ≤ t) (hthi : t ≤ 6/5) :
    0*t+((13/2)+-7*σ) ≤ energyClauseNineSecondRate σ*t := by
  have ha : 0*(4*σ-2)+((13/2)+-7*σ) ≤ energyClauseNineSecondRate σ*(4*σ-2) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  have hb : 0*(6/5)+((13/2)+-7*σ) ≤ energyClauseNineSecondRate σ*(6/5) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  exact energy_affine_le_mul_of_endpoints (4*σ-2) (6/5) t
    0 ((13/2)+-7*σ) (energyClauseNineSecondRate σ) htlo hthi ha hb

theorem energyClauseNine_short_diag_5 {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 4*σ-2 ≤ t) (hthi : t ≤ 6/5) :
    (2/5)*t+((28/5)+(-32/5)*σ) ≤ energyClauseNineSecondRate σ*t := by
  have ha : (2/5)*(4*σ-2)+((28/5)+(-32/5)*σ) ≤ energyClauseNineSecondRate σ*(4*σ-2) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  have hb : (2/5)*(6/5)+((28/5)+(-32/5)*σ) ≤ energyClauseNineSecondRate σ*(6/5) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  exact energy_affine_le_mul_of_endpoints (4*σ-2) (6/5) t
    (2/5) ((28/5)+(-32/5)*σ) (energyClauseNineSecondRate σ) htlo hthi ha hb

theorem energyClauseNine_short_diag_6 {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 4*σ-2 ≤ t) (hthi : t ≤ 6/5) :
    (1/2)*t+(4+(-9/2)*σ) ≤ energyClauseNineSecondRate σ*t := by
  have ha : (1/2)*(4*σ-2)+(4+(-9/2)*σ) ≤ energyClauseNineSecondRate σ*(4*σ-2) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  have hb : (1/2)*(6/5)+(4+(-9/2)*σ) ≤ energyClauseNineSecondRate σ*(6/5) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  exact energy_affine_le_mul_of_endpoints (4*σ-2) (6/5) t
    (1/2) (4+(-9/2)*σ) (energyClauseNineSecondRate σ) htlo hthi ha hb

theorem energyClauseNine_short_diag_7 {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 4*σ-2 ≤ t) (hthi : t ≤ 6/5) :
    (1/4)*t+((23/4)+(-25/4)*σ) ≤ energyClauseNineSecondRate σ*t := by
  have ha : (1/4)*(4*σ-2)+((23/4)+(-25/4)*σ) ≤ energyClauseNineSecondRate σ*(4*σ-2) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  have hb : (1/4)*(6/5)+((23/4)+(-25/4)*σ) ≤ energyClauseNineSecondRate σ*(6/5) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  exact energy_affine_le_mul_of_endpoints (4*σ-2) (6/5) t
    (1/4) ((23/4)+(-25/4)*σ) (energyClauseNineSecondRate σ) htlo hthi ha hb

theorem energyClauseNine_short_diag_8 {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 4*σ-2 ≤ t) (hthi : t ≤ 6/5) :
    (4/5)*t+((22/5)+(-26/5)*σ) ≤ energyClauseNineSecondRate σ*t := by
  have ha : (4/5)*(4*σ-2)+((22/5)+(-26/5)*σ) ≤ energyClauseNineSecondRate σ*(4*σ-2) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  have hb : (4/5)*(6/5)+((22/5)+(-26/5)*σ) ≤ energyClauseNineSecondRate σ*(6/5) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  exact energy_affine_le_mul_of_endpoints (4*σ-2) (6/5) t
    (4/5) ((22/5)+(-26/5)*σ) (energyClauseNineSecondRate σ) htlo hthi ha hb

theorem energyClauseNine_short_affine_0 {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 4*σ-2 ≤ t) (hthi : t ≤ 6/5) :
    1*t+((94/15)+(-124/15)*σ) ≤ energyClauseNineSecondRate σ*t := by
  have ha : 1*(4*σ-2)+((94/15)+(-124/15)*σ) ≤ energyClauseNineSecondRate σ*(4*σ-2) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  have hb : 1*(6/5)+((94/15)+(-124/15)*σ) ≤ energyClauseNineSecondRate σ*(6/5) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  exact energy_affine_le_mul_of_endpoints (4*σ-2) (6/5) t
    1 ((94/15)+(-124/15)*σ) (energyClauseNineSecondRate σ) htlo hthi ha hb

theorem energyClauseNine_short_affine_1 {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 4*σ-2 ≤ t) (hthi : t ≤ 6/5) :
    (5/2)*t+((39/4)+-15*σ) ≤ energyClauseNineSecondRate σ*t := by
  have ha : (5/2)*(4*σ-2)+((39/4)+-15*σ) ≤ energyClauseNineSecondRate σ*(4*σ-2) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  have hb : (5/2)*(6/5)+((39/4)+-15*σ) ≤ energyClauseNineSecondRate σ*(6/5) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  exact energy_affine_le_mul_of_endpoints (4*σ-2) (6/5) t
    (5/2) ((39/4)+-15*σ) (energyClauseNineSecondRate σ) htlo hthi ha hb

theorem energyClauseNine_short_affine_2 {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 4*σ-2 ≤ t) (hthi : t ≤ 6/5) :
    2*t+((174/25)+(-264/25)*σ) ≤ energyClauseNineSecondRate σ*t := by
  have ha : 2*(4*σ-2)+((174/25)+(-264/25)*σ) ≤ energyClauseNineSecondRate σ*(4*σ-2) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  have hb : 2*(6/5)+((174/25)+(-264/25)*σ) ≤ energyClauseNineSecondRate σ*(6/5) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  exact energy_affine_le_mul_of_endpoints (4*σ-2) (6/5) t
    2 ((174/25)+(-264/25)*σ) (energyClauseNineSecondRate σ) htlo hthi ha hb

theorem energyClauseNine_short_affine_3 {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 4*σ-2 ≤ t) (hthi : t ≤ 6/5) :
    2*t+((87/10)+(-66/5)*σ) ≤ energyClauseNineSecondRate σ*t := by
  have ha : 2*(4*σ-2)+((87/10)+(-66/5)*σ) ≤ energyClauseNineSecondRate σ*(4*σ-2) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  have hb : 2*(6/5)+((87/10)+(-66/5)*σ) ≤ energyClauseNineSecondRate σ*(6/5) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  exact energy_affine_le_mul_of_endpoints (4*σ-2) (6/5) t
    2 ((87/10)+(-66/5)*σ) (energyClauseNineSecondRate σ) htlo hthi ha hb

theorem energyClauseNine_short_affine_4 {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 4*σ-2 ≤ t) (hthi : t ≤ 6/5) :
    3*t+((113/10)+(-89/5)*σ) ≤ energyClauseNineSecondRate σ*t := by
  have ha : 3*(4*σ-2)+((113/10)+(-89/5)*σ) ≤ energyClauseNineSecondRate σ*(4*σ-2) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  have hb : 3*(6/5)+((113/10)+(-89/5)*σ) ≤ energyClauseNineSecondRate σ*(6/5) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  exact energy_affine_le_mul_of_endpoints (4*σ-2) (6/5) t
    3 ((113/10)+(-89/5)*σ) (energyClauseNineSecondRate σ) htlo hthi ha hb

theorem energyClauseNine_short_affine_5 {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 4*σ-2 ≤ t) (hthi : t ≤ 6/5) :
    (14/5)*t+((236/25)+(-376/25)*σ) ≤ energyClauseNineSecondRate σ*t := by
  have ha : (14/5)*(4*σ-2)+((236/25)+(-376/25)*σ) ≤ energyClauseNineSecondRate σ*(4*σ-2) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  have hb : (14/5)*(6/5)+((236/25)+(-376/25)*σ) ≤ energyClauseNineSecondRate σ*(6/5) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  exact energy_affine_le_mul_of_endpoints (4*σ-2) (6/5) t
    (14/5) ((236/25)+(-376/25)*σ) (energyClauseNineSecondRate σ) htlo hthi ha hb

theorem energyClauseNine_short_affine_6 {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 4*σ-2 ≤ t) (hthi : t ≤ 6/5) :
    (7/4)*t+(6+-9*σ) ≤ energyClauseNineSecondRate σ*t := by
  have ha : (7/4)*(4*σ-2)+(6+-9*σ) ≤ energyClauseNineSecondRate σ*(4*σ-2) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  have hb : (7/4)*(6/5)+(6+-9*σ) ≤ energyClauseNineSecondRate σ*(6/5) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  exact energy_affine_le_mul_of_endpoints (4*σ-2) (6/5) t
    (7/4) (6+-9*σ) (energyClauseNineSecondRate σ) htlo hthi ha hb

theorem energyClauseNine_short_affine_7 {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 4*σ-2 ≤ t) (hthi : t ≤ 6/5) :
    (23/8)*t+((199/20)+(-157/10)*σ) ≤ energyClauseNineSecondRate σ*t := by
  have ha : (23/8)*(4*σ-2)+((199/20)+(-157/10)*σ) ≤ energyClauseNineSecondRate σ*(4*σ-2) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  have hb : (23/8)*(6/5)+((199/20)+(-157/10)*σ) ≤ energyClauseNineSecondRate σ*(6/5) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  exact energy_affine_le_mul_of_endpoints (4*σ-2) (6/5) t
    (23/8) ((199/20)+(-157/10)*σ) (energyClauseNineSecondRate σ) htlo hthi ha hb

theorem energyClauseNine_short_affine_8 {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 4*σ-2 ≤ t) (hthi : t ≤ 6/5) :
    (13/5)*t+((182/25)+(-292/25)*σ) ≤ energyClauseNineSecondRate σ*t := by
  have ha : (13/5)*(4*σ-2)+((182/25)+(-292/25)*σ) ≤ energyClauseNineSecondRate σ*(4*σ-2) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  have hb : (13/5)*(6/5)+((182/25)+(-292/25)*σ) ≤ energyClauseNineSecondRate σ*(6/5) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  exact energy_affine_le_mul_of_endpoints (4*σ-2) (6/5) t
    (13/5) ((182/25)+(-292/25)*σ) (energyClauseNineSecondRate σ) htlo hthi ha hb

end TaoTrudgianYang2025
