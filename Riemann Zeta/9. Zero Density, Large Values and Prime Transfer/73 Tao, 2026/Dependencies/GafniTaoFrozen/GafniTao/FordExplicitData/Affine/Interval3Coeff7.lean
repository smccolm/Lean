import GafniTao.FordExplicitData.Affine.Interval3Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapAffineSource3_coeff_56 :
    fordGapAffineSource3.coeff 56 =
      fordGapAffineCoeff3 56 := by
  unfold fordGapAffineSource3
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 56 fordNumericalGapExplicit (33 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3]

@[simp] theorem fordGapAffineSource3_coeff_57 :
    fordGapAffineSource3.coeff 57 =
      fordGapAffineCoeff3 57 := by
  unfold fordGapAffineSource3
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 57 fordNumericalGapExplicit (33 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3]

@[simp] theorem fordGapAffineSource3_coeff_58 :
    fordGapAffineSource3.coeff 58 =
      fordGapAffineCoeff3 58 := by
  unfold fordGapAffineSource3
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 58 fordNumericalGapExplicit (33 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3]

@[simp] theorem fordGapAffineSource3_coeff_59 :
    fordGapAffineSource3.coeff 59 =
      fordGapAffineCoeff3 59 := by
  unfold fordGapAffineSource3
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 59 fordNumericalGapExplicit (33 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3]

@[simp] theorem fordGapAffineSource3_coeff_60 :
    fordGapAffineSource3.coeff 60 =
      fordGapAffineCoeff3 60 := by
  unfold fordGapAffineSource3
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 60 fordNumericalGapExplicit (33 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3]

@[simp] theorem fordGapAffineSource3_coeff_61 :
    fordGapAffineSource3.coeff 61 =
      fordGapAffineCoeff3 61 := by
  unfold fordGapAffineSource3
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 61 fordNumericalGapExplicit (33 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3]

@[simp] theorem fordGapAffineSource3_coeff_62 :
    fordGapAffineSource3.coeff 62 =
      fordGapAffineCoeff3 62 := by
  unfold fordGapAffineSource3
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 62 fordNumericalGapExplicit (33 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3]

@[simp] theorem fordGapAffineSource3_coeff_63 :
    fordGapAffineSource3.coeff 63 =
      fordGapAffineCoeff3 63 := by
  unfold fordGapAffineSource3
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 63 fordNumericalGapExplicit (33 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3]

end

end GafniTao
