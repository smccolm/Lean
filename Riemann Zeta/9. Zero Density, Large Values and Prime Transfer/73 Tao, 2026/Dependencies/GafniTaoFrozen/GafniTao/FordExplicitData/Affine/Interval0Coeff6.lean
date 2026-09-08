import GafniTao.FordExplicitData.Affine.Interval0Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapAffineSource0_coeff_48 :
    fordGapAffineSource0.coeff 48 =
      fordGapAffineCoeff0 48 := by
  unfold fordGapAffineSource0
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 48 fordNumericalGapExplicit (0 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff0]

@[simp] theorem fordGapAffineSource0_coeff_49 :
    fordGapAffineSource0.coeff 49 =
      fordGapAffineCoeff0 49 := by
  unfold fordGapAffineSource0
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 49 fordNumericalGapExplicit (0 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff0]

@[simp] theorem fordGapAffineSource0_coeff_50 :
    fordGapAffineSource0.coeff 50 =
      fordGapAffineCoeff0 50 := by
  unfold fordGapAffineSource0
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 50 fordNumericalGapExplicit (0 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff0]

@[simp] theorem fordGapAffineSource0_coeff_51 :
    fordGapAffineSource0.coeff 51 =
      fordGapAffineCoeff0 51 := by
  unfold fordGapAffineSource0
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 51 fordNumericalGapExplicit (0 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff0]

@[simp] theorem fordGapAffineSource0_coeff_52 :
    fordGapAffineSource0.coeff 52 =
      fordGapAffineCoeff0 52 := by
  unfold fordGapAffineSource0
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 52 fordNumericalGapExplicit (0 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff0]

@[simp] theorem fordGapAffineSource0_coeff_53 :
    fordGapAffineSource0.coeff 53 =
      fordGapAffineCoeff0 53 := by
  unfold fordGapAffineSource0
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 53 fordNumericalGapExplicit (0 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff0]

@[simp] theorem fordGapAffineSource0_coeff_54 :
    fordGapAffineSource0.coeff 54 =
      fordGapAffineCoeff0 54 := by
  unfold fordGapAffineSource0
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 54 fordNumericalGapExplicit (0 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff0]

@[simp] theorem fordGapAffineSource0_coeff_55 :
    fordGapAffineSource0.coeff 55 =
      fordGapAffineCoeff0 55 := by
  unfold fordGapAffineSource0
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 55 fordNumericalGapExplicit (0 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff0]

end

end GafniTao
