import GafniTao.FordExplicitData.Affine.Interval6Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapAffineSource6_coeff_16 :
    fordGapAffineSource6.coeff 16 =
      fordGapAffineCoeff6 16 := by
  unfold fordGapAffineSource6
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 16 fordNumericalGapExplicit (33 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6]

@[simp] theorem fordGapAffineSource6_coeff_17 :
    fordGapAffineSource6.coeff 17 =
      fordGapAffineCoeff6 17 := by
  unfold fordGapAffineSource6
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 17 fordNumericalGapExplicit (33 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6]

@[simp] theorem fordGapAffineSource6_coeff_18 :
    fordGapAffineSource6.coeff 18 =
      fordGapAffineCoeff6 18 := by
  unfold fordGapAffineSource6
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 18 fordNumericalGapExplicit (33 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6]

@[simp] theorem fordGapAffineSource6_coeff_19 :
    fordGapAffineSource6.coeff 19 =
      fordGapAffineCoeff6 19 := by
  unfold fordGapAffineSource6
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 19 fordNumericalGapExplicit (33 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6]

@[simp] theorem fordGapAffineSource6_coeff_20 :
    fordGapAffineSource6.coeff 20 =
      fordGapAffineCoeff6 20 := by
  unfold fordGapAffineSource6
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 20 fordNumericalGapExplicit (33 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6]

@[simp] theorem fordGapAffineSource6_coeff_21 :
    fordGapAffineSource6.coeff 21 =
      fordGapAffineCoeff6 21 := by
  unfold fordGapAffineSource6
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 21 fordNumericalGapExplicit (33 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6]

@[simp] theorem fordGapAffineSource6_coeff_22 :
    fordGapAffineSource6.coeff 22 =
      fordGapAffineCoeff6 22 := by
  unfold fordGapAffineSource6
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 22 fordNumericalGapExplicit (33 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6]

@[simp] theorem fordGapAffineSource6_coeff_23 :
    fordGapAffineSource6.coeff 23 =
      fordGapAffineCoeff6 23 := by
  unfold fordGapAffineSource6
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 23 fordNumericalGapExplicit (33 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6]

end

end GafniTao
