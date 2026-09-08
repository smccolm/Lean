import GafniTao.FordExplicitData.Affine.Interval6Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapAffineSource6_coeff_56 :
    fordGapAffineSource6.coeff 56 =
      fordGapAffineCoeff6 56 := by
  unfold fordGapAffineSource6
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 56 fordNumericalGapExplicit (33 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6]

@[simp] theorem fordGapAffineSource6_coeff_57 :
    fordGapAffineSource6.coeff 57 =
      fordGapAffineCoeff6 57 := by
  unfold fordGapAffineSource6
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 57 fordNumericalGapExplicit (33 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6]

@[simp] theorem fordGapAffineSource6_coeff_58 :
    fordGapAffineSource6.coeff 58 =
      fordGapAffineCoeff6 58 := by
  unfold fordGapAffineSource6
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 58 fordNumericalGapExplicit (33 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6]

@[simp] theorem fordGapAffineSource6_coeff_59 :
    fordGapAffineSource6.coeff 59 =
      fordGapAffineCoeff6 59 := by
  unfold fordGapAffineSource6
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 59 fordNumericalGapExplicit (33 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6]

@[simp] theorem fordGapAffineSource6_coeff_60 :
    fordGapAffineSource6.coeff 60 =
      fordGapAffineCoeff6 60 := by
  unfold fordGapAffineSource6
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 60 fordNumericalGapExplicit (33 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6]

@[simp] theorem fordGapAffineSource6_coeff_61 :
    fordGapAffineSource6.coeff 61 =
      fordGapAffineCoeff6 61 := by
  unfold fordGapAffineSource6
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 61 fordNumericalGapExplicit (33 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6]

@[simp] theorem fordGapAffineSource6_coeff_62 :
    fordGapAffineSource6.coeff 62 =
      fordGapAffineCoeff6 62 := by
  unfold fordGapAffineSource6
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 62 fordNumericalGapExplicit (33 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6]

@[simp] theorem fordGapAffineSource6_coeff_63 :
    fordGapAffineSource6.coeff 63 =
      fordGapAffineCoeff6 63 := by
  unfold fordGapAffineSource6
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 63 fordNumericalGapExplicit (33 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6]

end

end GafniTao
