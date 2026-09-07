import GafniTao.FordExplicitData.Affine.Interval7Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapAffineSource7_coeff_88 :
    fordGapAffineSource7.coeff 88 =
      fordGapAffineCoeff7 88 := by
  unfold fordGapAffineSource7
  rw [coeff_comp_affine,
    hasseDeriv_eval_eq_sum_range 88 88 fordNumericalGapExplicit (77 / 80 : ℚ)
      fordNumericalGapExplicit_natDegree_le]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7]

end

end GafniTao
