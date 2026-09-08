import GafniTao.FordExplicitData.Affine.Interval5Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapAffineSource5_coeff_24 :
    fordGapAffineSource5.coeff 24 =
      fordGapAffineCoeff5 24 := by
  unfold fordGapAffineSource5
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 24 fordNumericalGapExplicit (11 / 16 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5]

@[simp] theorem fordGapAffineSource5_coeff_25 :
    fordGapAffineSource5.coeff 25 =
      fordGapAffineCoeff5 25 := by
  unfold fordGapAffineSource5
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 25 fordNumericalGapExplicit (11 / 16 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5]

@[simp] theorem fordGapAffineSource5_coeff_26 :
    fordGapAffineSource5.coeff 26 =
      fordGapAffineCoeff5 26 := by
  unfold fordGapAffineSource5
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 26 fordNumericalGapExplicit (11 / 16 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5]

@[simp] theorem fordGapAffineSource5_coeff_27 :
    fordGapAffineSource5.coeff 27 =
      fordGapAffineCoeff5 27 := by
  unfold fordGapAffineSource5
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 27 fordNumericalGapExplicit (11 / 16 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5]

@[simp] theorem fordGapAffineSource5_coeff_28 :
    fordGapAffineSource5.coeff 28 =
      fordGapAffineCoeff5 28 := by
  unfold fordGapAffineSource5
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 28 fordNumericalGapExplicit (11 / 16 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5]

@[simp] theorem fordGapAffineSource5_coeff_29 :
    fordGapAffineSource5.coeff 29 =
      fordGapAffineCoeff5 29 := by
  unfold fordGapAffineSource5
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 29 fordNumericalGapExplicit (11 / 16 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5]

@[simp] theorem fordGapAffineSource5_coeff_30 :
    fordGapAffineSource5.coeff 30 =
      fordGapAffineCoeff5 30 := by
  unfold fordGapAffineSource5
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 30 fordNumericalGapExplicit (11 / 16 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5]

@[simp] theorem fordGapAffineSource5_coeff_31 :
    fordGapAffineSource5.coeff 31 =
      fordGapAffineCoeff5 31 := by
  unfold fordGapAffineSource5
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 31 fordNumericalGapExplicit (11 / 16 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5]

end

end GafniTao
