import GafniTao.FordExplicitData.Affine.Interval5Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapAffineSource5_coeff_80 :
    fordGapAffineSource5.coeff 80 =
      fordGapAffineCoeff5 80 := by
  unfold fordGapAffineSource5
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 80 fordNumericalGapExplicit (11 / 16 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5]

@[simp] theorem fordGapAffineSource5_coeff_81 :
    fordGapAffineSource5.coeff 81 =
      fordGapAffineCoeff5 81 := by
  unfold fordGapAffineSource5
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 81 fordNumericalGapExplicit (11 / 16 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5]

@[simp] theorem fordGapAffineSource5_coeff_82 :
    fordGapAffineSource5.coeff 82 =
      fordGapAffineCoeff5 82 := by
  unfold fordGapAffineSource5
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 82 fordNumericalGapExplicit (11 / 16 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5]

@[simp] theorem fordGapAffineSource5_coeff_83 :
    fordGapAffineSource5.coeff 83 =
      fordGapAffineCoeff5 83 := by
  unfold fordGapAffineSource5
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 83 fordNumericalGapExplicit (11 / 16 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5]

@[simp] theorem fordGapAffineSource5_coeff_84 :
    fordGapAffineSource5.coeff 84 =
      fordGapAffineCoeff5 84 := by
  unfold fordGapAffineSource5
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 84 fordNumericalGapExplicit (11 / 16 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5]

@[simp] theorem fordGapAffineSource5_coeff_85 :
    fordGapAffineSource5.coeff 85 =
      fordGapAffineCoeff5 85 := by
  unfold fordGapAffineSource5
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 85 fordNumericalGapExplicit (11 / 16 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5]

@[simp] theorem fordGapAffineSource5_coeff_86 :
    fordGapAffineSource5.coeff 86 =
      fordGapAffineCoeff5 86 := by
  unfold fordGapAffineSource5
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 86 fordNumericalGapExplicit (11 / 16 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5]

@[simp] theorem fordGapAffineSource5_coeff_87 :
    fordGapAffineSource5.coeff 87 =
      fordGapAffineCoeff5 87 := by
  unfold fordGapAffineSource5
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 87 fordNumericalGapExplicit (11 / 16 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5]

end

end GafniTao
