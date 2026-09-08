import GafniTao.FordExplicitData.Affine.Interval3Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapAffineSource3_coeff_0 :
    fordGapAffineSource3.coeff 0 =
      fordGapAffineCoeff3 0 := by
  unfold fordGapAffineSource3
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 0 fordNumericalGapExplicit (33 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3]

@[simp] theorem fordGapAffineSource3_coeff_1 :
    fordGapAffineSource3.coeff 1 =
      fordGapAffineCoeff3 1 := by
  unfold fordGapAffineSource3
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 1 fordNumericalGapExplicit (33 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3]

@[simp] theorem fordGapAffineSource3_coeff_2 :
    fordGapAffineSource3.coeff 2 =
      fordGapAffineCoeff3 2 := by
  unfold fordGapAffineSource3
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 2 fordNumericalGapExplicit (33 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3]

@[simp] theorem fordGapAffineSource3_coeff_3 :
    fordGapAffineSource3.coeff 3 =
      fordGapAffineCoeff3 3 := by
  unfold fordGapAffineSource3
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 3 fordNumericalGapExplicit (33 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3]

@[simp] theorem fordGapAffineSource3_coeff_4 :
    fordGapAffineSource3.coeff 4 =
      fordGapAffineCoeff3 4 := by
  unfold fordGapAffineSource3
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 4 fordNumericalGapExplicit (33 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3]

@[simp] theorem fordGapAffineSource3_coeff_5 :
    fordGapAffineSource3.coeff 5 =
      fordGapAffineCoeff3 5 := by
  unfold fordGapAffineSource3
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 5 fordNumericalGapExplicit (33 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3]

@[simp] theorem fordGapAffineSource3_coeff_6 :
    fordGapAffineSource3.coeff 6 =
      fordGapAffineCoeff3 6 := by
  unfold fordGapAffineSource3
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 6 fordNumericalGapExplicit (33 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3]

@[simp] theorem fordGapAffineSource3_coeff_7 :
    fordGapAffineSource3.coeff 7 =
      fordGapAffineCoeff3 7 := by
  unfold fordGapAffineSource3
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 7 fordNumericalGapExplicit (33 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3]

end

end GafniTao
