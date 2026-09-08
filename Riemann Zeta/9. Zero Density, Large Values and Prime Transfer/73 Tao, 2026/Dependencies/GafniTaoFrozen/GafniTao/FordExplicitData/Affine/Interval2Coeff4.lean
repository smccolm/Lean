import GafniTao.FordExplicitData.Affine.Interval2Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapAffineSource2_coeff_32 :
    fordGapAffineSource2.coeff 32 =
      fordGapAffineCoeff2 32 := by
  unfold fordGapAffineSource2
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 32 fordNumericalGapExplicit (11 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2]

@[simp] theorem fordGapAffineSource2_coeff_33 :
    fordGapAffineSource2.coeff 33 =
      fordGapAffineCoeff2 33 := by
  unfold fordGapAffineSource2
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 33 fordNumericalGapExplicit (11 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2]

@[simp] theorem fordGapAffineSource2_coeff_34 :
    fordGapAffineSource2.coeff 34 =
      fordGapAffineCoeff2 34 := by
  unfold fordGapAffineSource2
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 34 fordNumericalGapExplicit (11 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2]

@[simp] theorem fordGapAffineSource2_coeff_35 :
    fordGapAffineSource2.coeff 35 =
      fordGapAffineCoeff2 35 := by
  unfold fordGapAffineSource2
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 35 fordNumericalGapExplicit (11 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2]

@[simp] theorem fordGapAffineSource2_coeff_36 :
    fordGapAffineSource2.coeff 36 =
      fordGapAffineCoeff2 36 := by
  unfold fordGapAffineSource2
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 36 fordNumericalGapExplicit (11 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2]

@[simp] theorem fordGapAffineSource2_coeff_37 :
    fordGapAffineSource2.coeff 37 =
      fordGapAffineCoeff2 37 := by
  unfold fordGapAffineSource2
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 37 fordNumericalGapExplicit (11 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2]

@[simp] theorem fordGapAffineSource2_coeff_38 :
    fordGapAffineSource2.coeff 38 =
      fordGapAffineCoeff2 38 := by
  unfold fordGapAffineSource2
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 38 fordNumericalGapExplicit (11 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2]

@[simp] theorem fordGapAffineSource2_coeff_39 :
    fordGapAffineSource2.coeff 39 =
      fordGapAffineCoeff2 39 := by
  unfold fordGapAffineSource2
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 39 fordNumericalGapExplicit (11 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2]

end

end GafniTao
