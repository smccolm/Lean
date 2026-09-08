import GafniTao.FordExplicitData.Affine.Interval4Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapAffineSource4_coeff_72 :
    fordGapAffineSource4.coeff 72 =
      fordGapAffineCoeff4 72 := by
  unfold fordGapAffineSource4
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 72 fordNumericalGapExplicit (11 / 20 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4]

@[simp] theorem fordGapAffineSource4_coeff_73 :
    fordGapAffineSource4.coeff 73 =
      fordGapAffineCoeff4 73 := by
  unfold fordGapAffineSource4
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 73 fordNumericalGapExplicit (11 / 20 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4]

@[simp] theorem fordGapAffineSource4_coeff_74 :
    fordGapAffineSource4.coeff 74 =
      fordGapAffineCoeff4 74 := by
  unfold fordGapAffineSource4
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 74 fordNumericalGapExplicit (11 / 20 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4]

@[simp] theorem fordGapAffineSource4_coeff_75 :
    fordGapAffineSource4.coeff 75 =
      fordGapAffineCoeff4 75 := by
  unfold fordGapAffineSource4
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 75 fordNumericalGapExplicit (11 / 20 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4]

@[simp] theorem fordGapAffineSource4_coeff_76 :
    fordGapAffineSource4.coeff 76 =
      fordGapAffineCoeff4 76 := by
  unfold fordGapAffineSource4
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 76 fordNumericalGapExplicit (11 / 20 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4]

@[simp] theorem fordGapAffineSource4_coeff_77 :
    fordGapAffineSource4.coeff 77 =
      fordGapAffineCoeff4 77 := by
  unfold fordGapAffineSource4
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 77 fordNumericalGapExplicit (11 / 20 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4]

@[simp] theorem fordGapAffineSource4_coeff_78 :
    fordGapAffineSource4.coeff 78 =
      fordGapAffineCoeff4 78 := by
  unfold fordGapAffineSource4
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 78 fordNumericalGapExplicit (11 / 20 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4]

@[simp] theorem fordGapAffineSource4_coeff_79 :
    fordGapAffineSource4.coeff 79 =
      fordGapAffineCoeff4 79 := by
  unfold fordGapAffineSource4
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 79 fordNumericalGapExplicit (11 / 20 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4]

end

end GafniTao
