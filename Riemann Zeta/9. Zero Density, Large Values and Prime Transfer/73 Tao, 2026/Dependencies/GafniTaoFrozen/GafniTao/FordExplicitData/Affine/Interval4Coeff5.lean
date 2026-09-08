import GafniTao.FordExplicitData.Affine.Interval4Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapAffineSource4_coeff_40 :
    fordGapAffineSource4.coeff 40 =
      fordGapAffineCoeff4 40 := by
  unfold fordGapAffineSource4
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 40 fordNumericalGapExplicit (11 / 20 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4]

@[simp] theorem fordGapAffineSource4_coeff_41 :
    fordGapAffineSource4.coeff 41 =
      fordGapAffineCoeff4 41 := by
  unfold fordGapAffineSource4
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 41 fordNumericalGapExplicit (11 / 20 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4]

@[simp] theorem fordGapAffineSource4_coeff_42 :
    fordGapAffineSource4.coeff 42 =
      fordGapAffineCoeff4 42 := by
  unfold fordGapAffineSource4
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 42 fordNumericalGapExplicit (11 / 20 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4]

@[simp] theorem fordGapAffineSource4_coeff_43 :
    fordGapAffineSource4.coeff 43 =
      fordGapAffineCoeff4 43 := by
  unfold fordGapAffineSource4
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 43 fordNumericalGapExplicit (11 / 20 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4]

@[simp] theorem fordGapAffineSource4_coeff_44 :
    fordGapAffineSource4.coeff 44 =
      fordGapAffineCoeff4 44 := by
  unfold fordGapAffineSource4
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 44 fordNumericalGapExplicit (11 / 20 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4]

@[simp] theorem fordGapAffineSource4_coeff_45 :
    fordGapAffineSource4.coeff 45 =
      fordGapAffineCoeff4 45 := by
  unfold fordGapAffineSource4
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 45 fordNumericalGapExplicit (11 / 20 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4]

@[simp] theorem fordGapAffineSource4_coeff_46 :
    fordGapAffineSource4.coeff 46 =
      fordGapAffineCoeff4 46 := by
  unfold fordGapAffineSource4
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 46 fordNumericalGapExplicit (11 / 20 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4]

@[simp] theorem fordGapAffineSource4_coeff_47 :
    fordGapAffineSource4.coeff 47 =
      fordGapAffineCoeff4 47 := by
  unfold fordGapAffineSource4
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 47 fordNumericalGapExplicit (11 / 20 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4]

end

end GafniTao
