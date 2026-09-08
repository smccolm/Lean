import GafniTao.FordExplicitData.Affine.Interval2Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapAffineSource2_coeff_48 :
    fordGapAffineSource2.coeff 48 =
      fordGapAffineCoeff2 48 := by
  unfold fordGapAffineSource2
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 48 fordNumericalGapExplicit (11 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2]

@[simp] theorem fordGapAffineSource2_coeff_49 :
    fordGapAffineSource2.coeff 49 =
      fordGapAffineCoeff2 49 := by
  unfold fordGapAffineSource2
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 49 fordNumericalGapExplicit (11 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2]

@[simp] theorem fordGapAffineSource2_coeff_50 :
    fordGapAffineSource2.coeff 50 =
      fordGapAffineCoeff2 50 := by
  unfold fordGapAffineSource2
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 50 fordNumericalGapExplicit (11 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2]

@[simp] theorem fordGapAffineSource2_coeff_51 :
    fordGapAffineSource2.coeff 51 =
      fordGapAffineCoeff2 51 := by
  unfold fordGapAffineSource2
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 51 fordNumericalGapExplicit (11 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2]

@[simp] theorem fordGapAffineSource2_coeff_52 :
    fordGapAffineSource2.coeff 52 =
      fordGapAffineCoeff2 52 := by
  unfold fordGapAffineSource2
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 52 fordNumericalGapExplicit (11 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2]

@[simp] theorem fordGapAffineSource2_coeff_53 :
    fordGapAffineSource2.coeff 53 =
      fordGapAffineCoeff2 53 := by
  unfold fordGapAffineSource2
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 53 fordNumericalGapExplicit (11 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2]

@[simp] theorem fordGapAffineSource2_coeff_54 :
    fordGapAffineSource2.coeff 54 =
      fordGapAffineCoeff2 54 := by
  unfold fordGapAffineSource2
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 54 fordNumericalGapExplicit (11 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2]

@[simp] theorem fordGapAffineSource2_coeff_55 :
    fordGapAffineSource2.coeff 55 =
      fordGapAffineCoeff2 55 := by
  unfold fordGapAffineSource2
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 55 fordNumericalGapExplicit (11 / 40 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2]

end

end GafniTao
