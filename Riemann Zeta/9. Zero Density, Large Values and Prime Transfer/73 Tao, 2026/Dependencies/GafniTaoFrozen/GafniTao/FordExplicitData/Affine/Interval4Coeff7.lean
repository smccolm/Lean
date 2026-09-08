import GafniTao.FordExplicitData.Affine.Interval4Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapAffineSource4_coeff_56 :
    fordGapAffineSource4.coeff 56 =
      fordGapAffineCoeff4 56 := by
  unfold fordGapAffineSource4
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 56 fordNumericalGapExplicit (11 / 20 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4]

@[simp] theorem fordGapAffineSource4_coeff_57 :
    fordGapAffineSource4.coeff 57 =
      fordGapAffineCoeff4 57 := by
  unfold fordGapAffineSource4
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 57 fordNumericalGapExplicit (11 / 20 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4]

@[simp] theorem fordGapAffineSource4_coeff_58 :
    fordGapAffineSource4.coeff 58 =
      fordGapAffineCoeff4 58 := by
  unfold fordGapAffineSource4
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 58 fordNumericalGapExplicit (11 / 20 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4]

@[simp] theorem fordGapAffineSource4_coeff_59 :
    fordGapAffineSource4.coeff 59 =
      fordGapAffineCoeff4 59 := by
  unfold fordGapAffineSource4
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 59 fordNumericalGapExplicit (11 / 20 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4]

@[simp] theorem fordGapAffineSource4_coeff_60 :
    fordGapAffineSource4.coeff 60 =
      fordGapAffineCoeff4 60 := by
  unfold fordGapAffineSource4
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 60 fordNumericalGapExplicit (11 / 20 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4]

@[simp] theorem fordGapAffineSource4_coeff_61 :
    fordGapAffineSource4.coeff 61 =
      fordGapAffineCoeff4 61 := by
  unfold fordGapAffineSource4
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 61 fordNumericalGapExplicit (11 / 20 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4]

@[simp] theorem fordGapAffineSource4_coeff_62 :
    fordGapAffineSource4.coeff 62 =
      fordGapAffineCoeff4 62 := by
  unfold fordGapAffineSource4
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 62 fordNumericalGapExplicit (11 / 20 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4]

@[simp] theorem fordGapAffineSource4_coeff_63 :
    fordGapAffineSource4.coeff 63 =
      fordGapAffineCoeff4 63 := by
  unfold fordGapAffineSource4
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 63 fordNumericalGapExplicit (11 / 20 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4]

end

end GafniTao
