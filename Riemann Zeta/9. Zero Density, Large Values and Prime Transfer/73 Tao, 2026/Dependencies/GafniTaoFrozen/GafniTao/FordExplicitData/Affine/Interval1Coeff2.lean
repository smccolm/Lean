import GafniTao.FordExplicitData.Affine.Interval1Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapAffineSource1_coeff_16 :
    fordGapAffineSource1.coeff 16 =
      fordGapAffineCoeff1 16 := by
  unfold fordGapAffineSource1
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 16 fordNumericalGapExplicit (11 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1]

@[simp] theorem fordGapAffineSource1_coeff_17 :
    fordGapAffineSource1.coeff 17 =
      fordGapAffineCoeff1 17 := by
  unfold fordGapAffineSource1
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 17 fordNumericalGapExplicit (11 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1]

@[simp] theorem fordGapAffineSource1_coeff_18 :
    fordGapAffineSource1.coeff 18 =
      fordGapAffineCoeff1 18 := by
  unfold fordGapAffineSource1
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 18 fordNumericalGapExplicit (11 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1]

@[simp] theorem fordGapAffineSource1_coeff_19 :
    fordGapAffineSource1.coeff 19 =
      fordGapAffineCoeff1 19 := by
  unfold fordGapAffineSource1
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 19 fordNumericalGapExplicit (11 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1]

@[simp] theorem fordGapAffineSource1_coeff_20 :
    fordGapAffineSource1.coeff 20 =
      fordGapAffineCoeff1 20 := by
  unfold fordGapAffineSource1
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 20 fordNumericalGapExplicit (11 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1]

@[simp] theorem fordGapAffineSource1_coeff_21 :
    fordGapAffineSource1.coeff 21 =
      fordGapAffineCoeff1 21 := by
  unfold fordGapAffineSource1
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 21 fordNumericalGapExplicit (11 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1]

@[simp] theorem fordGapAffineSource1_coeff_22 :
    fordGapAffineSource1.coeff 22 =
      fordGapAffineCoeff1 22 := by
  unfold fordGapAffineSource1
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 22 fordNumericalGapExplicit (11 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1]

@[simp] theorem fordGapAffineSource1_coeff_23 :
    fordGapAffineSource1.coeff 23 =
      fordGapAffineCoeff1 23 := by
  unfold fordGapAffineSource1
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 23 fordNumericalGapExplicit (11 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1]

end

end GafniTao
