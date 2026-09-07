import GafniTao.FordExplicitData.Affine.Interval1Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapAffineSource1_coeff_0 :
    fordGapAffineSource1.coeff 0 =
      fordGapAffineCoeff1 0 := by
  unfold fordGapAffineSource1
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 0 fordNumericalGapExplicit (11 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1]

@[simp] theorem fordGapAffineSource1_coeff_1 :
    fordGapAffineSource1.coeff 1 =
      fordGapAffineCoeff1 1 := by
  unfold fordGapAffineSource1
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 1 fordNumericalGapExplicit (11 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1]

@[simp] theorem fordGapAffineSource1_coeff_2 :
    fordGapAffineSource1.coeff 2 =
      fordGapAffineCoeff1 2 := by
  unfold fordGapAffineSource1
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 2 fordNumericalGapExplicit (11 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1]

@[simp] theorem fordGapAffineSource1_coeff_3 :
    fordGapAffineSource1.coeff 3 =
      fordGapAffineCoeff1 3 := by
  unfold fordGapAffineSource1
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 3 fordNumericalGapExplicit (11 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1]

@[simp] theorem fordGapAffineSource1_coeff_4 :
    fordGapAffineSource1.coeff 4 =
      fordGapAffineCoeff1 4 := by
  unfold fordGapAffineSource1
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 4 fordNumericalGapExplicit (11 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1]

@[simp] theorem fordGapAffineSource1_coeff_5 :
    fordGapAffineSource1.coeff 5 =
      fordGapAffineCoeff1 5 := by
  unfold fordGapAffineSource1
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 5 fordNumericalGapExplicit (11 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1]

@[simp] theorem fordGapAffineSource1_coeff_6 :
    fordGapAffineSource1.coeff 6 =
      fordGapAffineCoeff1 6 := by
  unfold fordGapAffineSource1
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 6 fordNumericalGapExplicit (11 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1]

@[simp] theorem fordGapAffineSource1_coeff_7 :
    fordGapAffineSource1.coeff 7 =
      fordGapAffineCoeff1 7 := by
  unfold fordGapAffineSource1
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 7 fordNumericalGapExplicit (11 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1]

end

end GafniTao
