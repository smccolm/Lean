import GafniTao.FordExplicitData.Affine.Interval5Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapAffineSource5_coeff_88 :
    fordGapAffineSource5.coeff 88 =
      fordGapAffineCoeff5 88 := by
  unfold fordGapAffineSource5
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 88 fordNumericalGapExplicit (11 / 16 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5]

end

end GafniTao
