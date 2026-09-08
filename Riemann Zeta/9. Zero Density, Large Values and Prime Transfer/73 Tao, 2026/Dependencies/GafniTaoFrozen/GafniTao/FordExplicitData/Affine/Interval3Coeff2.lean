import GafniTao.FordExplicitData.Affine.Interval3Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapAffineSource3_coeff_16 :
    fordGapAffineSource3.coeff 16 =
      fordGapAffineCoeff3 16 := by
  unfold fordGapAffineSource3
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 16 fordNumericalGapExplicit (33 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3]

@[simp] theorem fordGapAffineSource3_coeff_17 :
    fordGapAffineSource3.coeff 17 =
      fordGapAffineCoeff3 17 := by
  unfold fordGapAffineSource3
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 17 fordNumericalGapExplicit (33 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3]

@[simp] theorem fordGapAffineSource3_coeff_18 :
    fordGapAffineSource3.coeff 18 =
      fordGapAffineCoeff3 18 := by
  unfold fordGapAffineSource3
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 18 fordNumericalGapExplicit (33 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3]

@[simp] theorem fordGapAffineSource3_coeff_19 :
    fordGapAffineSource3.coeff 19 =
      fordGapAffineCoeff3 19 := by
  unfold fordGapAffineSource3
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 19 fordNumericalGapExplicit (33 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3]

@[simp] theorem fordGapAffineSource3_coeff_20 :
    fordGapAffineSource3.coeff 20 =
      fordGapAffineCoeff3 20 := by
  unfold fordGapAffineSource3
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 20 fordNumericalGapExplicit (33 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3]

@[simp] theorem fordGapAffineSource3_coeff_21 :
    fordGapAffineSource3.coeff 21 =
      fordGapAffineCoeff3 21 := by
  unfold fordGapAffineSource3
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 21 fordNumericalGapExplicit (33 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3]

@[simp] theorem fordGapAffineSource3_coeff_22 :
    fordGapAffineSource3.coeff 22 =
      fordGapAffineCoeff3 22 := by
  unfold fordGapAffineSource3
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 22 fordNumericalGapExplicit (33 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3]

@[simp] theorem fordGapAffineSource3_coeff_23 :
    fordGapAffineSource3.coeff 23 =
      fordGapAffineCoeff3 23 := by
  unfold fordGapAffineSource3
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 23 fordNumericalGapExplicit (33 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3]

end

end GafniTao
