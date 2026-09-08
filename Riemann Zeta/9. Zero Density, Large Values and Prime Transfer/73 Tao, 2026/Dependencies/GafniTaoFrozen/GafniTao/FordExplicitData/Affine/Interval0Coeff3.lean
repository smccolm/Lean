import GafniTao.FordExplicitData.Affine.Interval0Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapAffineSource0_coeff_24 :
    fordGapAffineSource0.coeff 24 =
      fordGapAffineCoeff0 24 := by
  unfold fordGapAffineSource0
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 24 fordNumericalGapExplicit (0 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff0]

@[simp] theorem fordGapAffineSource0_coeff_25 :
    fordGapAffineSource0.coeff 25 =
      fordGapAffineCoeff0 25 := by
  unfold fordGapAffineSource0
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 25 fordNumericalGapExplicit (0 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff0]

@[simp] theorem fordGapAffineSource0_coeff_26 :
    fordGapAffineSource0.coeff 26 =
      fordGapAffineCoeff0 26 := by
  unfold fordGapAffineSource0
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 26 fordNumericalGapExplicit (0 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff0]

@[simp] theorem fordGapAffineSource0_coeff_27 :
    fordGapAffineSource0.coeff 27 =
      fordGapAffineCoeff0 27 := by
  unfold fordGapAffineSource0
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 27 fordNumericalGapExplicit (0 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff0]

@[simp] theorem fordGapAffineSource0_coeff_28 :
    fordGapAffineSource0.coeff 28 =
      fordGapAffineCoeff0 28 := by
  unfold fordGapAffineSource0
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 28 fordNumericalGapExplicit (0 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff0]

@[simp] theorem fordGapAffineSource0_coeff_29 :
    fordGapAffineSource0.coeff 29 =
      fordGapAffineCoeff0 29 := by
  unfold fordGapAffineSource0
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 29 fordNumericalGapExplicit (0 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff0]

@[simp] theorem fordGapAffineSource0_coeff_30 :
    fordGapAffineSource0.coeff 30 =
      fordGapAffineCoeff0 30 := by
  unfold fordGapAffineSource0
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 30 fordNumericalGapExplicit (0 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff0]

@[simp] theorem fordGapAffineSource0_coeff_31 :
    fordGapAffineSource0.coeff 31 =
      fordGapAffineCoeff0 31 := by
  unfold fordGapAffineSource0
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 31 fordNumericalGapExplicit (0 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff0]

end

end GafniTao
