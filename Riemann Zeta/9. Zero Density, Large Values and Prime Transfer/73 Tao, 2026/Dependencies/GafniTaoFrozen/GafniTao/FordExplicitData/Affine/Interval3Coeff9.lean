import GafniTao.FordExplicitData.Affine.Interval3Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapAffineSource3_coeff_72 :
    fordGapAffineSource3.coeff 72 =
      fordGapAffineCoeff3 72 := by
  unfold fordGapAffineSource3
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 72 fordNumericalGapExplicit (33 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3]

@[simp] theorem fordGapAffineSource3_coeff_73 :
    fordGapAffineSource3.coeff 73 =
      fordGapAffineCoeff3 73 := by
  unfold fordGapAffineSource3
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 73 fordNumericalGapExplicit (33 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3]

@[simp] theorem fordGapAffineSource3_coeff_74 :
    fordGapAffineSource3.coeff 74 =
      fordGapAffineCoeff3 74 := by
  unfold fordGapAffineSource3
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 74 fordNumericalGapExplicit (33 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3]

@[simp] theorem fordGapAffineSource3_coeff_75 :
    fordGapAffineSource3.coeff 75 =
      fordGapAffineCoeff3 75 := by
  unfold fordGapAffineSource3
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 75 fordNumericalGapExplicit (33 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3]

@[simp] theorem fordGapAffineSource3_coeff_76 :
    fordGapAffineSource3.coeff 76 =
      fordGapAffineCoeff3 76 := by
  unfold fordGapAffineSource3
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 76 fordNumericalGapExplicit (33 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3]

@[simp] theorem fordGapAffineSource3_coeff_77 :
    fordGapAffineSource3.coeff 77 =
      fordGapAffineCoeff3 77 := by
  unfold fordGapAffineSource3
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 77 fordNumericalGapExplicit (33 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3]

@[simp] theorem fordGapAffineSource3_coeff_78 :
    fordGapAffineSource3.coeff 78 =
      fordGapAffineCoeff3 78 := by
  unfold fordGapAffineSource3
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 78 fordNumericalGapExplicit (33 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3]

@[simp] theorem fordGapAffineSource3_coeff_79 :
    fordGapAffineSource3.coeff 79 =
      fordGapAffineCoeff3 79 := by
  unfold fordGapAffineSource3
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 79 fordNumericalGapExplicit (33 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3]

end

end GafniTao
