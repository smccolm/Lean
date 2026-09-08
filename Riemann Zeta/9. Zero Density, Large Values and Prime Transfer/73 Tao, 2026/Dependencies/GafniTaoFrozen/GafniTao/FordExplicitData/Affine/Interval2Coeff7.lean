import GafniTao.FordExplicitData.Affine.Interval2Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapAffineSource2_coeff_56 :
    fordGapAffineSource2.coeff 56 =
      fordGapAffineCoeff2 56 := by
  unfold fordGapAffineSource2
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 56 fordNumericalGapExplicit (11 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2]

@[simp] theorem fordGapAffineSource2_coeff_57 :
    fordGapAffineSource2.coeff 57 =
      fordGapAffineCoeff2 57 := by
  unfold fordGapAffineSource2
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 57 fordNumericalGapExplicit (11 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2]

@[simp] theorem fordGapAffineSource2_coeff_58 :
    fordGapAffineSource2.coeff 58 =
      fordGapAffineCoeff2 58 := by
  unfold fordGapAffineSource2
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 58 fordNumericalGapExplicit (11 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2]

@[simp] theorem fordGapAffineSource2_coeff_59 :
    fordGapAffineSource2.coeff 59 =
      fordGapAffineCoeff2 59 := by
  unfold fordGapAffineSource2
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 59 fordNumericalGapExplicit (11 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2]

@[simp] theorem fordGapAffineSource2_coeff_60 :
    fordGapAffineSource2.coeff 60 =
      fordGapAffineCoeff2 60 := by
  unfold fordGapAffineSource2
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 60 fordNumericalGapExplicit (11 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2]

@[simp] theorem fordGapAffineSource2_coeff_61 :
    fordGapAffineSource2.coeff 61 =
      fordGapAffineCoeff2 61 := by
  unfold fordGapAffineSource2
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 61 fordNumericalGapExplicit (11 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2]

@[simp] theorem fordGapAffineSource2_coeff_62 :
    fordGapAffineSource2.coeff 62 =
      fordGapAffineCoeff2 62 := by
  unfold fordGapAffineSource2
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 62 fordNumericalGapExplicit (11 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2]

@[simp] theorem fordGapAffineSource2_coeff_63 :
    fordGapAffineSource2.coeff 63 =
      fordGapAffineCoeff2 63 := by
  unfold fordGapAffineSource2
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 63 fordNumericalGapExplicit (11 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2]

end

end GafniTao
