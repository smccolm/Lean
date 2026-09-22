import TaoTrudgianYang2025.EnergyClauseNineRates

/-! Exact closed-interval certificates for Add-est (ix).
Every displayed rational inequality is checked by the Lean kernel. -/

noncomputable section

namespace TaoTrudgianYang2025

theorem energyClauseNine_middle_low_diag_0 {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 17/22)
    (htlo : 6/5 ≤ t) (hthi : t ≤ (81-96*σ)/5) :
    0*t+(6+-6*σ) ≤ energyClauseNineFirstRate σ*t := by
  have ha : 0*(6/5)+(6+-6*σ) ≤ energyClauseNineFirstRate σ*(6/5) := by
    unfold energyClauseNineFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 9*(3*σ-2))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (17/22)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((17/22)-σ)]
  have hb : 0*((81-96*σ)/5)+(6+-6*σ) ≤ energyClauseNineFirstRate σ*((81-96*σ)/5) := by
    unfold energyClauseNineFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 9*(3*σ-2))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (17/22)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((17/22)-σ)]
  exact energy_affine_le_mul_of_endpoints (6/5) ((81-96*σ)/5) t
    0 (6+-6*σ) (energyClauseNineFirstRate σ) htlo hthi ha hb

theorem energyClauseNine_middle_low_diag_1 {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 17/22)
    (htlo : 6/5 ≤ t) (hthi : t ≤ (81-96*σ)/5) :
    0*t+((13/2)+-7*σ) ≤ energyClauseNineFirstRate σ*t := by
  have ha : 0*(6/5)+((13/2)+-7*σ) ≤ energyClauseNineFirstRate σ*(6/5) := by
    unfold energyClauseNineFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 9*(3*σ-2))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (17/22)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((17/22)-σ)]
  have hb : 0*((81-96*σ)/5)+((13/2)+-7*σ) ≤ energyClauseNineFirstRate σ*((81-96*σ)/5) := by
    unfold energyClauseNineFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 9*(3*σ-2))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (17/22)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((17/22)-σ)]
  exact energy_affine_le_mul_of_endpoints (6/5) ((81-96*σ)/5) t
    0 ((13/2)+-7*σ) (energyClauseNineFirstRate σ) htlo hthi ha hb

theorem energyClauseNine_middle_low_affine_0 {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 17/22)
    (htlo : 6/5 ≤ t) (hthi : t ≤ (81-96*σ)/5) :
    1*t+((38/5)+(-48/5)*σ) ≤ energyClauseNineFirstRate σ*t := by
  have ha : 1*(6/5)+((38/5)+(-48/5)*σ) ≤ energyClauseNineFirstRate σ*(6/5) := by
    unfold energyClauseNineFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 9*(3*σ-2))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (17/22)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((17/22)-σ)]
  have hb : 1*((81-96*σ)/5)+((38/5)+(-48/5)*σ) ≤ energyClauseNineFirstRate σ*((81-96*σ)/5) := by
    unfold energyClauseNineFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 9*(3*σ-2))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (17/22)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((17/22)-σ)]
  exact energy_affine_le_mul_of_endpoints (6/5) ((81-96*σ)/5) t
    1 ((38/5)+(-48/5)*σ) (energyClauseNineFirstRate σ) htlo hthi ha hb

theorem energyClauseNine_middle_low_affine_1 {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 17/22)
    (htlo : 6/5 ≤ t) (hthi : t ≤ (81-96*σ)/5) :
    (5/2)*t+((21/2)+-16*σ) ≤ energyClauseNineFirstRate σ*t := by
  have ha : (5/2)*(6/5)+((21/2)+-16*σ) ≤ energyClauseNineFirstRate σ*(6/5) := by
    unfold energyClauseNineFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 9*(3*σ-2))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (17/22)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((17/22)-σ)]
  have hb : (5/2)*((81-96*σ)/5)+((21/2)+-16*σ) ≤ energyClauseNineFirstRate σ*((81-96*σ)/5) := by
    unfold energyClauseNineFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 9*(3*σ-2))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (17/22)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((17/22)-σ)]
  exact energy_affine_le_mul_of_endpoints (6/5) ((81-96*σ)/5) t
    (5/2) ((21/2)+-16*σ) (energyClauseNineFirstRate σ) htlo hthi ha hb

theorem energyClauseNine_middle_high_diag_0 {σ t : ℝ}
    (hlo : 17/22 ≤ σ)
    (htlo : 6/5 ≤ t) (hthi : t ≤ (13-8*σ)/5) :
    0*t+(6+-6*σ) ≤ energyClauseNineSecondRate σ*t := by
  have ha : 0*(6/5)+(6+-6*σ) ≤ energyClauseNineSecondRate σ*(6/5) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [sq_nonneg (σ-(17/22))]
  have hb : 0*((13-8*σ)/5)+(6+-6*σ) ≤ energyClauseNineSecondRate σ*((13-8*σ)/5) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [sq_nonneg (σ-(17/22))]
  exact energy_affine_le_mul_of_endpoints (6/5) ((13-8*σ)/5) t
    0 (6+-6*σ) (energyClauseNineSecondRate σ) htlo hthi ha hb

theorem energyClauseNine_middle_high_diag_1 {σ t : ℝ}
    (hlo : 17/22 ≤ σ)
    (htlo : 6/5 ≤ t) (hthi : t ≤ (13-8*σ)/5) :
    0*t+((13/2)+-7*σ) ≤ energyClauseNineSecondRate σ*t := by
  have ha : 0*(6/5)+((13/2)+-7*σ) ≤ energyClauseNineSecondRate σ*(6/5) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [sq_nonneg (σ-(17/22))]
  have hb : 0*((13-8*σ)/5)+((13/2)+-7*σ) ≤ energyClauseNineSecondRate σ*((13-8*σ)/5) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [sq_nonneg (σ-(17/22))]
  exact energy_affine_le_mul_of_endpoints (6/5) ((13-8*σ)/5) t
    0 ((13/2)+-7*σ) (energyClauseNineSecondRate σ) htlo hthi ha hb

theorem energyClauseNine_middle_high_affine_0 {σ t : ℝ}
    (hlo : 17/22 ≤ σ)
    (htlo : 6/5 ≤ t) (hthi : t ≤ (13-8*σ)/5) :
    1*t+((38/5)+(-48/5)*σ) ≤ energyClauseNineSecondRate σ*t := by
  have ha : 1*(6/5)+((38/5)+(-48/5)*σ) ≤ energyClauseNineSecondRate σ*(6/5) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [sq_nonneg (σ-(17/22))]
  have hb : 1*((13-8*σ)/5)+((38/5)+(-48/5)*σ) ≤ energyClauseNineSecondRate σ*((13-8*σ)/5) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [sq_nonneg (σ-(17/22))]
  exact energy_affine_le_mul_of_endpoints (6/5) ((13-8*σ)/5) t
    1 ((38/5)+(-48/5)*σ) (energyClauseNineSecondRate σ) htlo hthi ha hb

theorem energyClauseNine_middle_high_affine_1 {σ t : ℝ}
    (hlo : 17/22 ≤ σ)
    (htlo : 6/5 ≤ t) (hthi : t ≤ (13-8*σ)/5) :
    (5/2)*t+((21/2)+-16*σ) ≤ energyClauseNineSecondRate σ*t := by
  have ha : (5/2)*(6/5)+((21/2)+-16*σ) ≤ energyClauseNineSecondRate σ*(6/5) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [sq_nonneg (σ-(17/22))]
  have hb : (5/2)*((13-8*σ)/5)+((21/2)+-16*σ) ≤ energyClauseNineSecondRate σ*((13-8*σ)/5) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [sq_nonneg (σ-(17/22))]
  exact energy_affine_le_mul_of_endpoints (6/5) ((13-8*σ)/5) t
    (5/2) ((21/2)+-16*σ) (energyClauseNineSecondRate σ) htlo hthi ha hb

theorem energyClauseNine_middle_first_0 {σ t : ℝ}
    (hlo : 17/22 ≤ σ)
    (htlo : (13-8*σ)/5 ≤ t) (hthi : t ≤ (4+4*σ)/5) :
    (1/3)*t+((28/3)+(-32/3)*σ) ≤ energyClauseNineSecondRate σ*t := by
  have ha : (1/3)*((13-8*σ)/5)+((28/3)+(-32/3)*σ) ≤ energyClauseNineSecondRate σ*((13-8*σ)/5) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [sq_nonneg (σ-(17/22))]
  have hb : (1/3)*((4+4*σ)/5)+((28/3)+(-32/3)*σ) ≤ energyClauseNineSecondRate σ*((4+4*σ)/5) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [sq_nonneg (σ-(17/22))]
  exact energy_affine_le_mul_of_endpoints ((13-8*σ)/5) ((4+4*σ)/5) t
    (1/3) ((28/3)+(-32/3)*σ) (energyClauseNineSecondRate σ) htlo hthi ha hb

theorem energyClauseNine_middle_first_1 {σ t : ℝ}
    (hlo : 17/22 ≤ σ)
    (htlo : (13-8*σ)/5 ≤ t) (hthi : t ≤ (4+4*σ)/5) :
    (5/6)*t+((89/6)+(-56/3)*σ) ≤ energyClauseNineSecondRate σ*t := by
  have ha : (5/6)*((13-8*σ)/5)+((89/6)+(-56/3)*σ) ≤ energyClauseNineSecondRate σ*((13-8*σ)/5) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [sq_nonneg (σ-(17/22))]
  have hb : (5/6)*((4+4*σ)/5)+((89/6)+(-56/3)*σ) ≤ energyClauseNineSecondRate σ*((4+4*σ)/5) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [sq_nonneg (σ-(17/22))]
  exact energy_affine_le_mul_of_endpoints ((13-8*σ)/5) ((4+4*σ)/5) t
    (5/6) ((89/6)+(-56/3)*σ) (energyClauseNineSecondRate σ) htlo hthi ha hb

theorem energyClauseNine_middle_ninth_0 {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 16*σ-11 ≤ t) (hthi : t ≤ (27*σ-18)/2) :
    (2/3)*t+(13+-16*σ) ≤ energyClauseNineFirstRate σ*t := by
  have ha : (2/3)*(16*σ-11)+(13+-16*σ) ≤ energyClauseNineFirstRate σ*(16*σ-11) := by
    unfold energyClauseNineFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 9*(3*σ-2))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  have hb : (2/3)*((27*σ-18)/2)+(13+-16*σ) ≤ energyClauseNineFirstRate σ*((27*σ-18)/2) := by
    unfold energyClauseNineFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 9*(3*σ-2))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  exact energy_affine_le_mul_of_endpoints (16*σ-11) ((27*σ-18)/2) t
    (2/3) (13+-16*σ) (energyClauseNineFirstRate σ) htlo hthi ha hb

theorem energyClauseNine_middle_ninth_1 {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 16*σ-11 ≤ t) (hthi : t ≤ (27*σ-18)/2) :
    (5/3)*t+(24+-32*σ) ≤ energyClauseNineFirstRate σ*t := by
  have ha : (5/3)*(16*σ-11)+(24+-32*σ) ≤ energyClauseNineFirstRate σ*(16*σ-11) := by
    unfold energyClauseNineFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 9*(3*σ-2))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  have hb : (5/3)*((27*σ-18)/2)+(24+-32*σ) ≤ energyClauseNineFirstRate σ*((27*σ-18)/2) := by
    unfold energyClauseNineFirstRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 9*(3*σ-2))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  exact energy_affine_le_mul_of_endpoints (16*σ-11) ((27*σ-18)/2) t
    (5/3) (24+-32*σ) (energyClauseNineFirstRate σ) htlo hthi ha hb

theorem energyClauseNine_middle_mixed_0 {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : (4+4*σ)/5 ≤ t) (hthi : t ≤ (16*σ-8)/3) :
    (3/4)*t+(9+-11*σ) ≤ energyClauseNineSecondRate σ*t := by
  have ha : (3/4)*((4+4*σ)/5)+(9+-11*σ) ≤ energyClauseNineSecondRate σ*((4+4*σ)/5) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  have hb : (3/4)*((16*σ-8)/3)+(9+-11*σ) ≤ energyClauseNineSecondRate σ*((16*σ-8)/3) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  exact energy_affine_le_mul_of_endpoints ((4+4*σ)/5) ((16*σ-8)/3) t
    (3/4) (9+-11*σ) (energyClauseNineSecondRate σ) htlo hthi ha hb

theorem energyClauseNine_middle_mixed_1 {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : (4+4*σ)/5 ≤ t) (hthi : t ≤ (16*σ-8)/3) :
    (15/8)*t+(14+(-39/2)*σ) ≤ energyClauseNineSecondRate σ*t := by
  have ha : (15/8)*((4+4*σ)/5)+(14+(-39/2)*σ) ≤ energyClauseNineSecondRate σ*((4+4*σ)/5) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  have hb : (15/8)*((16*σ-8)/3)+(14+(-39/2)*σ) ≤ energyClauseNineSecondRate σ*((16*σ-8)/3) := by
    unfold energyClauseNineSecondRate
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ-(84/109))
      (by linarith : 0 ≤ (4/5)-σ),
      sq_nonneg (σ-(84/109)), sq_nonneg ((4/5)-σ)]
  exact energy_affine_le_mul_of_endpoints ((4+4*σ)/5) ((16*σ-8)/3) t
    (15/8) (14+(-39/2)*σ) (energyClauseNineSecondRate σ) htlo hthi ha hb

end TaoTrudgianYang2025
