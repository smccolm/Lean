import GafniTao.FordExplicitData.Affine.Interval5Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapAffineSource5_coeff_8 :
    fordGapAffineSource5.coeff 8 =
      fordGapAffineCoeff5 8 := by
  unfold fordGapAffineSource5
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 8 fordNumericalGapExplicit (11 / 16 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5]

@[simp] theorem fordGapAffineSource5_coeff_9 :
    fordGapAffineSource5.coeff 9 =
      fordGapAffineCoeff5 9 := by
  unfold fordGapAffineSource5
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 9 fordNumericalGapExplicit (11 / 16 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5]

@[simp] theorem fordGapAffineSource5_coeff_10 :
    fordGapAffineSource5.coeff 10 =
      fordGapAffineCoeff5 10 := by
  unfold fordGapAffineSource5
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 10 fordNumericalGapExplicit (11 / 16 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5]

@[simp] theorem fordGapAffineSource5_coeff_11 :
    fordGapAffineSource5.coeff 11 =
      fordGapAffineCoeff5 11 := by
  unfold fordGapAffineSource5
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 11 fordNumericalGapExplicit (11 / 16 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5]

@[simp] theorem fordGapAffineSource5_coeff_12 :
    fordGapAffineSource5.coeff 12 =
      fordGapAffineCoeff5 12 := by
  unfold fordGapAffineSource5
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 12 fordNumericalGapExplicit (11 / 16 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5]

@[simp] theorem fordGapAffineSource5_coeff_13 :
    fordGapAffineSource5.coeff 13 =
      fordGapAffineCoeff5 13 := by
  unfold fordGapAffineSource5
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 13 fordNumericalGapExplicit (11 / 16 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5]

@[simp] theorem fordGapAffineSource5_coeff_14 :
    fordGapAffineSource5.coeff 14 =
      fordGapAffineCoeff5 14 := by
  unfold fordGapAffineSource5
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 14 fordNumericalGapExplicit (11 / 16 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5]

@[simp] theorem fordGapAffineSource5_coeff_15 :
    fordGapAffineSource5.coeff 15 =
      fordGapAffineCoeff5 15 := by
  unfold fordGapAffineSource5
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 15 fordNumericalGapExplicit (11 / 16 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5]

end

end GafniTao
