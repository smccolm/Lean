import GafniTao.FordExplicitData.Affine.Interval1Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapAffineSource1_coeff_40 :
    fordGapAffineSource1.coeff 40 =
      fordGapAffineCoeff1 40 := by
  unfold fordGapAffineSource1
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 40 fordNumericalGapExplicit (11 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1]

@[simp] theorem fordGapAffineSource1_coeff_41 :
    fordGapAffineSource1.coeff 41 =
      fordGapAffineCoeff1 41 := by
  unfold fordGapAffineSource1
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 41 fordNumericalGapExplicit (11 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1]

@[simp] theorem fordGapAffineSource1_coeff_42 :
    fordGapAffineSource1.coeff 42 =
      fordGapAffineCoeff1 42 := by
  unfold fordGapAffineSource1
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 42 fordNumericalGapExplicit (11 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1]

@[simp] theorem fordGapAffineSource1_coeff_43 :
    fordGapAffineSource1.coeff 43 =
      fordGapAffineCoeff1 43 := by
  unfold fordGapAffineSource1
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 43 fordNumericalGapExplicit (11 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1]

@[simp] theorem fordGapAffineSource1_coeff_44 :
    fordGapAffineSource1.coeff 44 =
      fordGapAffineCoeff1 44 := by
  unfold fordGapAffineSource1
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 44 fordNumericalGapExplicit (11 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1]

@[simp] theorem fordGapAffineSource1_coeff_45 :
    fordGapAffineSource1.coeff 45 =
      fordGapAffineCoeff1 45 := by
  unfold fordGapAffineSource1
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 45 fordNumericalGapExplicit (11 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1]

@[simp] theorem fordGapAffineSource1_coeff_46 :
    fordGapAffineSource1.coeff 46 =
      fordGapAffineCoeff1 46 := by
  unfold fordGapAffineSource1
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 46 fordNumericalGapExplicit (11 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1]

@[simp] theorem fordGapAffineSource1_coeff_47 :
    fordGapAffineSource1.coeff 47 =
      fordGapAffineCoeff1 47 := by
  unfold fordGapAffineSource1
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 47 fordNumericalGapExplicit (11 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1]

end

end GafniTao
