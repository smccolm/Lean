import GafniTao.FordExplicitData.Affine.Interval6Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapAffineSource6_coeff_0 :
    fordGapAffineSource6.coeff 0 =
      fordGapAffineCoeff6 0 := by
  unfold fordGapAffineSource6
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 0 fordNumericalGapExplicit (33 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6]

@[simp] theorem fordGapAffineSource6_coeff_1 :
    fordGapAffineSource6.coeff 1 =
      fordGapAffineCoeff6 1 := by
  unfold fordGapAffineSource6
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 1 fordNumericalGapExplicit (33 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6]

@[simp] theorem fordGapAffineSource6_coeff_2 :
    fordGapAffineSource6.coeff 2 =
      fordGapAffineCoeff6 2 := by
  unfold fordGapAffineSource6
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 2 fordNumericalGapExplicit (33 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6]

@[simp] theorem fordGapAffineSource6_coeff_3 :
    fordGapAffineSource6.coeff 3 =
      fordGapAffineCoeff6 3 := by
  unfold fordGapAffineSource6
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 3 fordNumericalGapExplicit (33 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6]

@[simp] theorem fordGapAffineSource6_coeff_4 :
    fordGapAffineSource6.coeff 4 =
      fordGapAffineCoeff6 4 := by
  unfold fordGapAffineSource6
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 4 fordNumericalGapExplicit (33 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6]

@[simp] theorem fordGapAffineSource6_coeff_5 :
    fordGapAffineSource6.coeff 5 =
      fordGapAffineCoeff6 5 := by
  unfold fordGapAffineSource6
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 5 fordNumericalGapExplicit (33 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6]

@[simp] theorem fordGapAffineSource6_coeff_6 :
    fordGapAffineSource6.coeff 6 =
      fordGapAffineCoeff6 6 := by
  unfold fordGapAffineSource6
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 6 fordNumericalGapExplicit (33 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6]

@[simp] theorem fordGapAffineSource6_coeff_7 :
    fordGapAffineSource6.coeff 7 =
      fordGapAffineCoeff6 7 := by
  unfold fordGapAffineSource6
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 7 fordNumericalGapExplicit (33 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6]

end

end GafniTao
