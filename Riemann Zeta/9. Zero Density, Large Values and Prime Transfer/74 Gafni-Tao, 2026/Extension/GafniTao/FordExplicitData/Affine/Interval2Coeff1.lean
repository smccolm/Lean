import GafniTao.FordExplicitData.Affine.Interval2Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapAffineSource2_coeff_8 :
    fordGapAffineSource2.coeff 8 =
      fordGapAffineCoeff2 8 := by
  unfold fordGapAffineSource2
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 8 fordNumericalGapExplicit (11 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2]

@[simp] theorem fordGapAffineSource2_coeff_9 :
    fordGapAffineSource2.coeff 9 =
      fordGapAffineCoeff2 9 := by
  unfold fordGapAffineSource2
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 9 fordNumericalGapExplicit (11 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2]

@[simp] theorem fordGapAffineSource2_coeff_10 :
    fordGapAffineSource2.coeff 10 =
      fordGapAffineCoeff2 10 := by
  unfold fordGapAffineSource2
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 10 fordNumericalGapExplicit (11 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2]

@[simp] theorem fordGapAffineSource2_coeff_11 :
    fordGapAffineSource2.coeff 11 =
      fordGapAffineCoeff2 11 := by
  unfold fordGapAffineSource2
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 11 fordNumericalGapExplicit (11 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2]

@[simp] theorem fordGapAffineSource2_coeff_12 :
    fordGapAffineSource2.coeff 12 =
      fordGapAffineCoeff2 12 := by
  unfold fordGapAffineSource2
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 12 fordNumericalGapExplicit (11 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2]

@[simp] theorem fordGapAffineSource2_coeff_13 :
    fordGapAffineSource2.coeff 13 =
      fordGapAffineCoeff2 13 := by
  unfold fordGapAffineSource2
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 13 fordNumericalGapExplicit (11 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2]

@[simp] theorem fordGapAffineSource2_coeff_14 :
    fordGapAffineSource2.coeff 14 =
      fordGapAffineCoeff2 14 := by
  unfold fordGapAffineSource2
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 14 fordNumericalGapExplicit (11 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2]

@[simp] theorem fordGapAffineSource2_coeff_15 :
    fordGapAffineSource2.coeff 15 =
      fordGapAffineCoeff2 15 := by
  unfold fordGapAffineSource2
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 15 fordNumericalGapExplicit (11 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2]

end

end GafniTao
