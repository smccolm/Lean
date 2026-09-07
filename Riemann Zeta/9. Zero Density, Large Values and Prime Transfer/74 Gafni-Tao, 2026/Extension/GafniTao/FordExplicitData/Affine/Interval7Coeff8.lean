import GafniTao.FordExplicitData.Affine.Interval7Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapAffineSource7_coeff_64 :
    fordGapAffineSource7.coeff 64 =
      fordGapAffineCoeff7 64 := by
  unfold fordGapAffineSource7
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 64 fordNumericalGapExplicit (77 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7]

@[simp] theorem fordGapAffineSource7_coeff_65 :
    fordGapAffineSource7.coeff 65 =
      fordGapAffineCoeff7 65 := by
  unfold fordGapAffineSource7
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 65 fordNumericalGapExplicit (77 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7]

@[simp] theorem fordGapAffineSource7_coeff_66 :
    fordGapAffineSource7.coeff 66 =
      fordGapAffineCoeff7 66 := by
  unfold fordGapAffineSource7
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 66 fordNumericalGapExplicit (77 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7]

@[simp] theorem fordGapAffineSource7_coeff_67 :
    fordGapAffineSource7.coeff 67 =
      fordGapAffineCoeff7 67 := by
  unfold fordGapAffineSource7
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 67 fordNumericalGapExplicit (77 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7]

@[simp] theorem fordGapAffineSource7_coeff_68 :
    fordGapAffineSource7.coeff 68 =
      fordGapAffineCoeff7 68 := by
  unfold fordGapAffineSource7
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 68 fordNumericalGapExplicit (77 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7]

@[simp] theorem fordGapAffineSource7_coeff_69 :
    fordGapAffineSource7.coeff 69 =
      fordGapAffineCoeff7 69 := by
  unfold fordGapAffineSource7
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 69 fordNumericalGapExplicit (77 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7]

@[simp] theorem fordGapAffineSource7_coeff_70 :
    fordGapAffineSource7.coeff 70 =
      fordGapAffineCoeff7 70 := by
  unfold fordGapAffineSource7
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 70 fordNumericalGapExplicit (77 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7]

@[simp] theorem fordGapAffineSource7_coeff_71 :
    fordGapAffineSource7.coeff 71 =
      fordGapAffineCoeff7 71 := by
  unfold fordGapAffineSource7
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 71 fordNumericalGapExplicit (77 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7]

end

end GafniTao
