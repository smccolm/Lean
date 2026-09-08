import GafniTao.FordExplicitData.Affine.Interval4Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapAffineSource4_coeff_0 :
    fordGapAffineSource4.coeff 0 =
      fordGapAffineCoeff4 0 := by
  unfold fordGapAffineSource4
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 0 fordNumericalGapExplicit (11 / 20 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4]

@[simp] theorem fordGapAffineSource4_coeff_1 :
    fordGapAffineSource4.coeff 1 =
      fordGapAffineCoeff4 1 := by
  unfold fordGapAffineSource4
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 1 fordNumericalGapExplicit (11 / 20 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4]

@[simp] theorem fordGapAffineSource4_coeff_2 :
    fordGapAffineSource4.coeff 2 =
      fordGapAffineCoeff4 2 := by
  unfold fordGapAffineSource4
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 2 fordNumericalGapExplicit (11 / 20 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4]

@[simp] theorem fordGapAffineSource4_coeff_3 :
    fordGapAffineSource4.coeff 3 =
      fordGapAffineCoeff4 3 := by
  unfold fordGapAffineSource4
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 3 fordNumericalGapExplicit (11 / 20 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4]

@[simp] theorem fordGapAffineSource4_coeff_4 :
    fordGapAffineSource4.coeff 4 =
      fordGapAffineCoeff4 4 := by
  unfold fordGapAffineSource4
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 4 fordNumericalGapExplicit (11 / 20 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4]

@[simp] theorem fordGapAffineSource4_coeff_5 :
    fordGapAffineSource4.coeff 5 =
      fordGapAffineCoeff4 5 := by
  unfold fordGapAffineSource4
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 5 fordNumericalGapExplicit (11 / 20 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4]

@[simp] theorem fordGapAffineSource4_coeff_6 :
    fordGapAffineSource4.coeff 6 =
      fordGapAffineCoeff4 6 := by
  unfold fordGapAffineSource4
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 6 fordNumericalGapExplicit (11 / 20 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4]

@[simp] theorem fordGapAffineSource4_coeff_7 :
    fordGapAffineSource4.coeff 7 =
      fordGapAffineCoeff4 7 := by
  unfold fordGapAffineSource4
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 7 fordNumericalGapExplicit (11 / 20 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4]

end

end GafniTao
