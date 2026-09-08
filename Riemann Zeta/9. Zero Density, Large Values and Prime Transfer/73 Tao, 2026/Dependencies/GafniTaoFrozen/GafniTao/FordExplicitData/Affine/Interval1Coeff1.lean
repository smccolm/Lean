import GafniTao.FordExplicitData.Affine.Interval1Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapAffineSource1_coeff_8 :
    fordGapAffineSource1.coeff 8 =
      fordGapAffineCoeff1 8 := by
  unfold fordGapAffineSource1
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 8 fordNumericalGapExplicit (11 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1]

@[simp] theorem fordGapAffineSource1_coeff_9 :
    fordGapAffineSource1.coeff 9 =
      fordGapAffineCoeff1 9 := by
  unfold fordGapAffineSource1
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 9 fordNumericalGapExplicit (11 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1]

@[simp] theorem fordGapAffineSource1_coeff_10 :
    fordGapAffineSource1.coeff 10 =
      fordGapAffineCoeff1 10 := by
  unfold fordGapAffineSource1
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 10 fordNumericalGapExplicit (11 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1]

@[simp] theorem fordGapAffineSource1_coeff_11 :
    fordGapAffineSource1.coeff 11 =
      fordGapAffineCoeff1 11 := by
  unfold fordGapAffineSource1
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 11 fordNumericalGapExplicit (11 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1]

@[simp] theorem fordGapAffineSource1_coeff_12 :
    fordGapAffineSource1.coeff 12 =
      fordGapAffineCoeff1 12 := by
  unfold fordGapAffineSource1
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 12 fordNumericalGapExplicit (11 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1]

@[simp] theorem fordGapAffineSource1_coeff_13 :
    fordGapAffineSource1.coeff 13 =
      fordGapAffineCoeff1 13 := by
  unfold fordGapAffineSource1
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 13 fordNumericalGapExplicit (11 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1]

@[simp] theorem fordGapAffineSource1_coeff_14 :
    fordGapAffineSource1.coeff 14 =
      fordGapAffineCoeff1 14 := by
  unfold fordGapAffineSource1
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 14 fordNumericalGapExplicit (11 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1]

@[simp] theorem fordGapAffineSource1_coeff_15 :
    fordGapAffineSource1.coeff 15 =
      fordGapAffineCoeff1 15 := by
  unfold fordGapAffineSource1
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 15 fordNumericalGapExplicit (11 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1]

end

end GafniTao
