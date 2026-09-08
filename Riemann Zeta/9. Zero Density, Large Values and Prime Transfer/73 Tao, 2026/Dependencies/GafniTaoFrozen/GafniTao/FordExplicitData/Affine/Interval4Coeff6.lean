import GafniTao.FordExplicitData.Affine.Interval4Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapAffineSource4_coeff_48 :
    fordGapAffineSource4.coeff 48 =
      fordGapAffineCoeff4 48 := by
  unfold fordGapAffineSource4
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 48 fordNumericalGapExplicit (11 / 20 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4]

@[simp] theorem fordGapAffineSource4_coeff_49 :
    fordGapAffineSource4.coeff 49 =
      fordGapAffineCoeff4 49 := by
  unfold fordGapAffineSource4
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 49 fordNumericalGapExplicit (11 / 20 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4]

@[simp] theorem fordGapAffineSource4_coeff_50 :
    fordGapAffineSource4.coeff 50 =
      fordGapAffineCoeff4 50 := by
  unfold fordGapAffineSource4
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 50 fordNumericalGapExplicit (11 / 20 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4]

@[simp] theorem fordGapAffineSource4_coeff_51 :
    fordGapAffineSource4.coeff 51 =
      fordGapAffineCoeff4 51 := by
  unfold fordGapAffineSource4
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 51 fordNumericalGapExplicit (11 / 20 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4]

@[simp] theorem fordGapAffineSource4_coeff_52 :
    fordGapAffineSource4.coeff 52 =
      fordGapAffineCoeff4 52 := by
  unfold fordGapAffineSource4
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 52 fordNumericalGapExplicit (11 / 20 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4]

@[simp] theorem fordGapAffineSource4_coeff_53 :
    fordGapAffineSource4.coeff 53 =
      fordGapAffineCoeff4 53 := by
  unfold fordGapAffineSource4
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 53 fordNumericalGapExplicit (11 / 20 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4]

@[simp] theorem fordGapAffineSource4_coeff_54 :
    fordGapAffineSource4.coeff 54 =
      fordGapAffineCoeff4 54 := by
  unfold fordGapAffineSource4
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 54 fordNumericalGapExplicit (11 / 20 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4]

@[simp] theorem fordGapAffineSource4_coeff_55 :
    fordGapAffineSource4.coeff 55 =
      fordGapAffineCoeff4 55 := by
  unfold fordGapAffineSource4
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 55 fordNumericalGapExplicit (11 / 20 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4]

end

end GafniTao
