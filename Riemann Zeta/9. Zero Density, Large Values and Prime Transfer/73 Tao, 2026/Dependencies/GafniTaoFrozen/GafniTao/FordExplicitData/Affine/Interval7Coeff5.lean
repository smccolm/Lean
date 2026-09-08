import GafniTao.FordExplicitData.Affine.Interval7Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapAffineSource7_coeff_40 :
    fordGapAffineSource7.coeff 40 =
      fordGapAffineCoeff7 40 := by
  unfold fordGapAffineSource7
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 40 fordNumericalGapExplicit (77 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7]

@[simp] theorem fordGapAffineSource7_coeff_41 :
    fordGapAffineSource7.coeff 41 =
      fordGapAffineCoeff7 41 := by
  unfold fordGapAffineSource7
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 41 fordNumericalGapExplicit (77 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7]

@[simp] theorem fordGapAffineSource7_coeff_42 :
    fordGapAffineSource7.coeff 42 =
      fordGapAffineCoeff7 42 := by
  unfold fordGapAffineSource7
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 42 fordNumericalGapExplicit (77 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7]

@[simp] theorem fordGapAffineSource7_coeff_43 :
    fordGapAffineSource7.coeff 43 =
      fordGapAffineCoeff7 43 := by
  unfold fordGapAffineSource7
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 43 fordNumericalGapExplicit (77 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7]

@[simp] theorem fordGapAffineSource7_coeff_44 :
    fordGapAffineSource7.coeff 44 =
      fordGapAffineCoeff7 44 := by
  unfold fordGapAffineSource7
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 44 fordNumericalGapExplicit (77 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7]

@[simp] theorem fordGapAffineSource7_coeff_45 :
    fordGapAffineSource7.coeff 45 =
      fordGapAffineCoeff7 45 := by
  unfold fordGapAffineSource7
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 45 fordNumericalGapExplicit (77 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7]

@[simp] theorem fordGapAffineSource7_coeff_46 :
    fordGapAffineSource7.coeff 46 =
      fordGapAffineCoeff7 46 := by
  unfold fordGapAffineSource7
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 46 fordNumericalGapExplicit (77 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7]

@[simp] theorem fordGapAffineSource7_coeff_47 :
    fordGapAffineSource7.coeff 47 =
      fordGapAffineCoeff7 47 := by
  unfold fordGapAffineSource7
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 47 fordNumericalGapExplicit (77 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7]

end

end GafniTao
