import GafniTao.FordExplicitData.Affine.Interval0Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapAffineSource0_coeff_88 :
    fordGapAffineSource0.coeff 88 =
      fordGapAffineCoeff0 88 := by
  unfold fordGapAffineSource0
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 88 fordNumericalGapExplicit (0 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff0]

end

end GafniTao
