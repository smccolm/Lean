import GafniTao.FordExplicitData.Affine.Interval7Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapAffineSource7_coeff_24 :
    fordGapAffineSource7.coeff 24 =
      fordGapAffineCoeff7 24 := by
  unfold fordGapAffineSource7
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 24 fordNumericalGapExplicit (77 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7]

@[simp] theorem fordGapAffineSource7_coeff_25 :
    fordGapAffineSource7.coeff 25 =
      fordGapAffineCoeff7 25 := by
  unfold fordGapAffineSource7
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 25 fordNumericalGapExplicit (77 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7]

@[simp] theorem fordGapAffineSource7_coeff_26 :
    fordGapAffineSource7.coeff 26 =
      fordGapAffineCoeff7 26 := by
  unfold fordGapAffineSource7
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 26 fordNumericalGapExplicit (77 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7]

@[simp] theorem fordGapAffineSource7_coeff_27 :
    fordGapAffineSource7.coeff 27 =
      fordGapAffineCoeff7 27 := by
  unfold fordGapAffineSource7
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 27 fordNumericalGapExplicit (77 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7]

@[simp] theorem fordGapAffineSource7_coeff_28 :
    fordGapAffineSource7.coeff 28 =
      fordGapAffineCoeff7 28 := by
  unfold fordGapAffineSource7
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 28 fordNumericalGapExplicit (77 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7]

@[simp] theorem fordGapAffineSource7_coeff_29 :
    fordGapAffineSource7.coeff 29 =
      fordGapAffineCoeff7 29 := by
  unfold fordGapAffineSource7
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 29 fordNumericalGapExplicit (77 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7]

@[simp] theorem fordGapAffineSource7_coeff_30 :
    fordGapAffineSource7.coeff 30 =
      fordGapAffineCoeff7 30 := by
  unfold fordGapAffineSource7
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 30 fordNumericalGapExplicit (77 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7]

@[simp] theorem fordGapAffineSource7_coeff_31 :
    fordGapAffineSource7.coeff 31 =
      fordGapAffineCoeff7 31 := by
  unfold fordGapAffineSource7
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 31 fordNumericalGapExplicit (77 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7]

end

end GafniTao
