import GafniTao.FordExplicitData.Affine.Interval0Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapAffineSource0_coeff_80 :
    fordGapAffineSource0.coeff 80 =
      fordGapAffineCoeff0 80 := by
  unfold fordGapAffineSource0
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 80 fordNumericalGapExplicit (0 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff0]

@[simp] theorem fordGapAffineSource0_coeff_81 :
    fordGapAffineSource0.coeff 81 =
      fordGapAffineCoeff0 81 := by
  unfold fordGapAffineSource0
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 81 fordNumericalGapExplicit (0 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff0]

@[simp] theorem fordGapAffineSource0_coeff_82 :
    fordGapAffineSource0.coeff 82 =
      fordGapAffineCoeff0 82 := by
  unfold fordGapAffineSource0
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 82 fordNumericalGapExplicit (0 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff0]

@[simp] theorem fordGapAffineSource0_coeff_83 :
    fordGapAffineSource0.coeff 83 =
      fordGapAffineCoeff0 83 := by
  unfold fordGapAffineSource0
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 83 fordNumericalGapExplicit (0 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff0]

@[simp] theorem fordGapAffineSource0_coeff_84 :
    fordGapAffineSource0.coeff 84 =
      fordGapAffineCoeff0 84 := by
  unfold fordGapAffineSource0
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 84 fordNumericalGapExplicit (0 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff0]

@[simp] theorem fordGapAffineSource0_coeff_85 :
    fordGapAffineSource0.coeff 85 =
      fordGapAffineCoeff0 85 := by
  unfold fordGapAffineSource0
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 85 fordNumericalGapExplicit (0 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff0]

@[simp] theorem fordGapAffineSource0_coeff_86 :
    fordGapAffineSource0.coeff 86 =
      fordGapAffineCoeff0 86 := by
  unfold fordGapAffineSource0
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 86 fordNumericalGapExplicit (0 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff0]

@[simp] theorem fordGapAffineSource0_coeff_87 :
    fordGapAffineSource0.coeff 87 =
      fordGapAffineCoeff0 87 := by
  unfold fordGapAffineSource0
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 87 fordNumericalGapExplicit (0 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff0]

end

end GafniTao
