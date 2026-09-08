import GafniTao.FordExplicitData.Affine.Interval6Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapAffineSource6_coeff_64 :
    fordGapAffineSource6.coeff 64 =
      fordGapAffineCoeff6 64 := by
  unfold fordGapAffineSource6
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 64 fordNumericalGapExplicit (33 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6]

@[simp] theorem fordGapAffineSource6_coeff_65 :
    fordGapAffineSource6.coeff 65 =
      fordGapAffineCoeff6 65 := by
  unfold fordGapAffineSource6
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 65 fordNumericalGapExplicit (33 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6]

@[simp] theorem fordGapAffineSource6_coeff_66 :
    fordGapAffineSource6.coeff 66 =
      fordGapAffineCoeff6 66 := by
  unfold fordGapAffineSource6
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 66 fordNumericalGapExplicit (33 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6]

@[simp] theorem fordGapAffineSource6_coeff_67 :
    fordGapAffineSource6.coeff 67 =
      fordGapAffineCoeff6 67 := by
  unfold fordGapAffineSource6
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 67 fordNumericalGapExplicit (33 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6]

@[simp] theorem fordGapAffineSource6_coeff_68 :
    fordGapAffineSource6.coeff 68 =
      fordGapAffineCoeff6 68 := by
  unfold fordGapAffineSource6
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 68 fordNumericalGapExplicit (33 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6]

@[simp] theorem fordGapAffineSource6_coeff_69 :
    fordGapAffineSource6.coeff 69 =
      fordGapAffineCoeff6 69 := by
  unfold fordGapAffineSource6
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 69 fordNumericalGapExplicit (33 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6]

@[simp] theorem fordGapAffineSource6_coeff_70 :
    fordGapAffineSource6.coeff 70 =
      fordGapAffineCoeff6 70 := by
  unfold fordGapAffineSource6
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 70 fordNumericalGapExplicit (33 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6]

@[simp] theorem fordGapAffineSource6_coeff_71 :
    fordGapAffineSource6.coeff 71 =
      fordGapAffineCoeff6 71 := by
  unfold fordGapAffineSource6
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 71 fordNumericalGapExplicit (33 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6]

end

end GafniTao
