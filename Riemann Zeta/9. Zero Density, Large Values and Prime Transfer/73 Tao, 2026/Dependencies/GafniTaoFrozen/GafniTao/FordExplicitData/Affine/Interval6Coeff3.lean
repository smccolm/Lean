import GafniTao.FordExplicitData.Affine.Interval6Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapAffineSource6_coeff_24 :
    fordGapAffineSource6.coeff 24 =
      fordGapAffineCoeff6 24 := by
  unfold fordGapAffineSource6
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 24 fordNumericalGapExplicit (33 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6]

@[simp] theorem fordGapAffineSource6_coeff_25 :
    fordGapAffineSource6.coeff 25 =
      fordGapAffineCoeff6 25 := by
  unfold fordGapAffineSource6
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 25 fordNumericalGapExplicit (33 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6]

@[simp] theorem fordGapAffineSource6_coeff_26 :
    fordGapAffineSource6.coeff 26 =
      fordGapAffineCoeff6 26 := by
  unfold fordGapAffineSource6
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 26 fordNumericalGapExplicit (33 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6]

@[simp] theorem fordGapAffineSource6_coeff_27 :
    fordGapAffineSource6.coeff 27 =
      fordGapAffineCoeff6 27 := by
  unfold fordGapAffineSource6
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 27 fordNumericalGapExplicit (33 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6]

@[simp] theorem fordGapAffineSource6_coeff_28 :
    fordGapAffineSource6.coeff 28 =
      fordGapAffineCoeff6 28 := by
  unfold fordGapAffineSource6
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 28 fordNumericalGapExplicit (33 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6]

@[simp] theorem fordGapAffineSource6_coeff_29 :
    fordGapAffineSource6.coeff 29 =
      fordGapAffineCoeff6 29 := by
  unfold fordGapAffineSource6
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 29 fordNumericalGapExplicit (33 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6]

@[simp] theorem fordGapAffineSource6_coeff_30 :
    fordGapAffineSource6.coeff 30 =
      fordGapAffineCoeff6 30 := by
  unfold fordGapAffineSource6
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 30 fordNumericalGapExplicit (33 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6]

@[simp] theorem fordGapAffineSource6_coeff_31 :
    fordGapAffineSource6.coeff 31 =
      fordGapAffineCoeff6 31 := by
  unfold fordGapAffineSource6
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 31 fordNumericalGapExplicit (33 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6]

end

end GafniTao
