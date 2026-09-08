import GafniTao.FordExplicitData.Affine.Interval0Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapAffineSource0_coeff_16 :
    fordGapAffineSource0.coeff 16 =
      fordGapAffineCoeff0 16 := by
  unfold fordGapAffineSource0
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 16 fordNumericalGapExplicit (0 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff0]

@[simp] theorem fordGapAffineSource0_coeff_17 :
    fordGapAffineSource0.coeff 17 =
      fordGapAffineCoeff0 17 := by
  unfold fordGapAffineSource0
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 17 fordNumericalGapExplicit (0 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff0]

@[simp] theorem fordGapAffineSource0_coeff_18 :
    fordGapAffineSource0.coeff 18 =
      fordGapAffineCoeff0 18 := by
  unfold fordGapAffineSource0
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 18 fordNumericalGapExplicit (0 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff0]

@[simp] theorem fordGapAffineSource0_coeff_19 :
    fordGapAffineSource0.coeff 19 =
      fordGapAffineCoeff0 19 := by
  unfold fordGapAffineSource0
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 19 fordNumericalGapExplicit (0 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff0]

@[simp] theorem fordGapAffineSource0_coeff_20 :
    fordGapAffineSource0.coeff 20 =
      fordGapAffineCoeff0 20 := by
  unfold fordGapAffineSource0
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 20 fordNumericalGapExplicit (0 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff0]

@[simp] theorem fordGapAffineSource0_coeff_21 :
    fordGapAffineSource0.coeff 21 =
      fordGapAffineCoeff0 21 := by
  unfold fordGapAffineSource0
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 21 fordNumericalGapExplicit (0 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff0]

@[simp] theorem fordGapAffineSource0_coeff_22 :
    fordGapAffineSource0.coeff 22 =
      fordGapAffineCoeff0 22 := by
  unfold fordGapAffineSource0
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 22 fordNumericalGapExplicit (0 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff0]

@[simp] theorem fordGapAffineSource0_coeff_23 :
    fordGapAffineSource0.coeff 23 =
      fordGapAffineCoeff0 23 := by
  unfold fordGapAffineSource0
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 23 fordNumericalGapExplicit (0 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff0]

end

end GafniTao
