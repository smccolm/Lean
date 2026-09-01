import GafniTao.FordExplicitData.Affine.Interval7Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapAffineSource7_coeff_8 :
    fordGapAffineSource7.coeff 8 =
      fordGapAffineCoeff7 8 := by
  unfold fordGapAffineSource7
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 8 fordNumericalGapExplicit (77 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7]

@[simp] theorem fordGapAffineSource7_coeff_9 :
    fordGapAffineSource7.coeff 9 =
      fordGapAffineCoeff7 9 := by
  unfold fordGapAffineSource7
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 9 fordNumericalGapExplicit (77 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7]

@[simp] theorem fordGapAffineSource7_coeff_10 :
    fordGapAffineSource7.coeff 10 =
      fordGapAffineCoeff7 10 := by
  unfold fordGapAffineSource7
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 10 fordNumericalGapExplicit (77 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7]

@[simp] theorem fordGapAffineSource7_coeff_11 :
    fordGapAffineSource7.coeff 11 =
      fordGapAffineCoeff7 11 := by
  unfold fordGapAffineSource7
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 11 fordNumericalGapExplicit (77 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7]

@[simp] theorem fordGapAffineSource7_coeff_12 :
    fordGapAffineSource7.coeff 12 =
      fordGapAffineCoeff7 12 := by
  unfold fordGapAffineSource7
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 12 fordNumericalGapExplicit (77 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7]

@[simp] theorem fordGapAffineSource7_coeff_13 :
    fordGapAffineSource7.coeff 13 =
      fordGapAffineCoeff7 13 := by
  unfold fordGapAffineSource7
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 13 fordNumericalGapExplicit (77 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7]

@[simp] theorem fordGapAffineSource7_coeff_14 :
    fordGapAffineSource7.coeff 14 =
      fordGapAffineCoeff7 14 := by
  unfold fordGapAffineSource7
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 14 fordNumericalGapExplicit (77 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7]

@[simp] theorem fordGapAffineSource7_coeff_15 :
    fordGapAffineSource7.coeff 15 =
      fordGapAffineCoeff7 15 := by
  unfold fordGapAffineSource7
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 15 fordNumericalGapExplicit (77 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7]

end

end GafniTao
