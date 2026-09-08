import GafniTao.FordExplicitData.Affine.Interval5Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapAffineSource5_coeff_72 :
    fordGapAffineSource5.coeff 72 =
      fordGapAffineCoeff5 72 := by
  unfold fordGapAffineSource5
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 72 fordNumericalGapExplicit (11 / 16 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5]

@[simp] theorem fordGapAffineSource5_coeff_73 :
    fordGapAffineSource5.coeff 73 =
      fordGapAffineCoeff5 73 := by
  unfold fordGapAffineSource5
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 73 fordNumericalGapExplicit (11 / 16 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5]

@[simp] theorem fordGapAffineSource5_coeff_74 :
    fordGapAffineSource5.coeff 74 =
      fordGapAffineCoeff5 74 := by
  unfold fordGapAffineSource5
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 74 fordNumericalGapExplicit (11 / 16 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5]

@[simp] theorem fordGapAffineSource5_coeff_75 :
    fordGapAffineSource5.coeff 75 =
      fordGapAffineCoeff5 75 := by
  unfold fordGapAffineSource5
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 75 fordNumericalGapExplicit (11 / 16 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5]

@[simp] theorem fordGapAffineSource5_coeff_76 :
    fordGapAffineSource5.coeff 76 =
      fordGapAffineCoeff5 76 := by
  unfold fordGapAffineSource5
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 76 fordNumericalGapExplicit (11 / 16 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5]

@[simp] theorem fordGapAffineSource5_coeff_77 :
    fordGapAffineSource5.coeff 77 =
      fordGapAffineCoeff5 77 := by
  unfold fordGapAffineSource5
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 77 fordNumericalGapExplicit (11 / 16 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5]

@[simp] theorem fordGapAffineSource5_coeff_78 :
    fordGapAffineSource5.coeff 78 =
      fordGapAffineCoeff5 78 := by
  unfold fordGapAffineSource5
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 78 fordNumericalGapExplicit (11 / 16 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5]

@[simp] theorem fordGapAffineSource5_coeff_79 :
    fordGapAffineSource5.coeff 79 =
      fordGapAffineCoeff5 79 := by
  unfold fordGapAffineSource5
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 79 fordNumericalGapExplicit (11 / 16 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5]

end

end GafniTao
