import GafniTao.FordExplicitData.Affine.Interval3Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapAffineSource3_coeff_80 :
    fordGapAffineSource3.coeff 80 =
      fordGapAffineCoeff3 80 := by
  unfold fordGapAffineSource3
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 80 fordNumericalGapExplicit (33 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3]

@[simp] theorem fordGapAffineSource3_coeff_81 :
    fordGapAffineSource3.coeff 81 =
      fordGapAffineCoeff3 81 := by
  unfold fordGapAffineSource3
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 81 fordNumericalGapExplicit (33 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3]

@[simp] theorem fordGapAffineSource3_coeff_82 :
    fordGapAffineSource3.coeff 82 =
      fordGapAffineCoeff3 82 := by
  unfold fordGapAffineSource3
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 82 fordNumericalGapExplicit (33 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3]

@[simp] theorem fordGapAffineSource3_coeff_83 :
    fordGapAffineSource3.coeff 83 =
      fordGapAffineCoeff3 83 := by
  unfold fordGapAffineSource3
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 83 fordNumericalGapExplicit (33 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3]

@[simp] theorem fordGapAffineSource3_coeff_84 :
    fordGapAffineSource3.coeff 84 =
      fordGapAffineCoeff3 84 := by
  unfold fordGapAffineSource3
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 84 fordNumericalGapExplicit (33 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3]

@[simp] theorem fordGapAffineSource3_coeff_85 :
    fordGapAffineSource3.coeff 85 =
      fordGapAffineCoeff3 85 := by
  unfold fordGapAffineSource3
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 85 fordNumericalGapExplicit (33 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3]

@[simp] theorem fordGapAffineSource3_coeff_86 :
    fordGapAffineSource3.coeff 86 =
      fordGapAffineCoeff3 86 := by
  unfold fordGapAffineSource3
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 86 fordNumericalGapExplicit (33 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3]

@[simp] theorem fordGapAffineSource3_coeff_87 :
    fordGapAffineSource3.coeff 87 =
      fordGapAffineCoeff3 87 := by
  unfold fordGapAffineSource3
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 87 fordNumericalGapExplicit (33 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3]

end

end GafniTao
