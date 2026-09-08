import GafniTao.FordExplicitData.Affine.Interval2Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapAffineSource2_coeff_40 :
    fordGapAffineSource2.coeff 40 =
      fordGapAffineCoeff2 40 := by
  unfold fordGapAffineSource2
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 40 fordNumericalGapExplicit (11 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2]

@[simp] theorem fordGapAffineSource2_coeff_41 :
    fordGapAffineSource2.coeff 41 =
      fordGapAffineCoeff2 41 := by
  unfold fordGapAffineSource2
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 41 fordNumericalGapExplicit (11 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2]

@[simp] theorem fordGapAffineSource2_coeff_42 :
    fordGapAffineSource2.coeff 42 =
      fordGapAffineCoeff2 42 := by
  unfold fordGapAffineSource2
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 42 fordNumericalGapExplicit (11 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2]

@[simp] theorem fordGapAffineSource2_coeff_43 :
    fordGapAffineSource2.coeff 43 =
      fordGapAffineCoeff2 43 := by
  unfold fordGapAffineSource2
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 43 fordNumericalGapExplicit (11 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2]

@[simp] theorem fordGapAffineSource2_coeff_44 :
    fordGapAffineSource2.coeff 44 =
      fordGapAffineCoeff2 44 := by
  unfold fordGapAffineSource2
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 44 fordNumericalGapExplicit (11 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2]

@[simp] theorem fordGapAffineSource2_coeff_45 :
    fordGapAffineSource2.coeff 45 =
      fordGapAffineCoeff2 45 := by
  unfold fordGapAffineSource2
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 45 fordNumericalGapExplicit (11 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2]

@[simp] theorem fordGapAffineSource2_coeff_46 :
    fordGapAffineSource2.coeff 46 =
      fordGapAffineCoeff2 46 := by
  unfold fordGapAffineSource2
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 46 fordNumericalGapExplicit (11 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2]

@[simp] theorem fordGapAffineSource2_coeff_47 :
    fordGapAffineSource2.coeff 47 =
      fordGapAffineCoeff2 47 := by
  unfold fordGapAffineSource2
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 47 fordNumericalGapExplicit (11 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2]

end

end GafniTao
