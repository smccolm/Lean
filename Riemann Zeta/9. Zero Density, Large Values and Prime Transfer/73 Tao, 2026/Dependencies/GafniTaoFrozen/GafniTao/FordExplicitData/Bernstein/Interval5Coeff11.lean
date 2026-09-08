import GafniTao.FordExplicitData.Bernstein.Interval5Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapBernsteinSourceCoeff5_88 :
    polynomialBernsteinCoeff 88 fordGapAffineSource5 88 =
      fordGapBernsteinCoeff5 88 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5, fordGapBernsteinCoeff5]

end

end GafniTao
