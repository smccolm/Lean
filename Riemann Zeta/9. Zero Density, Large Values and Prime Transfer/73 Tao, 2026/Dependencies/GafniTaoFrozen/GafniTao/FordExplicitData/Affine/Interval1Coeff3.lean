import GafniTao.FordExplicitData.Affine.Interval1Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapAffineSource1_coeff_24 :
    fordGapAffineSource1.coeff 24 =
      fordGapAffineCoeff1 24 := by
  unfold fordGapAffineSource1
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 24 fordNumericalGapExplicit (11 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1]

@[simp] theorem fordGapAffineSource1_coeff_25 :
    fordGapAffineSource1.coeff 25 =
      fordGapAffineCoeff1 25 := by
  unfold fordGapAffineSource1
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 25 fordNumericalGapExplicit (11 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1]

@[simp] theorem fordGapAffineSource1_coeff_26 :
    fordGapAffineSource1.coeff 26 =
      fordGapAffineCoeff1 26 := by
  unfold fordGapAffineSource1
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 26 fordNumericalGapExplicit (11 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1]

@[simp] theorem fordGapAffineSource1_coeff_27 :
    fordGapAffineSource1.coeff 27 =
      fordGapAffineCoeff1 27 := by
  unfold fordGapAffineSource1
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 27 fordNumericalGapExplicit (11 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1]

@[simp] theorem fordGapAffineSource1_coeff_28 :
    fordGapAffineSource1.coeff 28 =
      fordGapAffineCoeff1 28 := by
  unfold fordGapAffineSource1
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 28 fordNumericalGapExplicit (11 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1]

@[simp] theorem fordGapAffineSource1_coeff_29 :
    fordGapAffineSource1.coeff 29 =
      fordGapAffineCoeff1 29 := by
  unfold fordGapAffineSource1
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 29 fordNumericalGapExplicit (11 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1]

@[simp] theorem fordGapAffineSource1_coeff_30 :
    fordGapAffineSource1.coeff 30 =
      fordGapAffineCoeff1 30 := by
  unfold fordGapAffineSource1
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 30 fordNumericalGapExplicit (11 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1]

@[simp] theorem fordGapAffineSource1_coeff_31 :
    fordGapAffineSource1.coeff 31 =
      fordGapAffineCoeff1 31 := by
  unfold fordGapAffineSource1
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 31 fordNumericalGapExplicit (11 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1]

end

end GafniTao
