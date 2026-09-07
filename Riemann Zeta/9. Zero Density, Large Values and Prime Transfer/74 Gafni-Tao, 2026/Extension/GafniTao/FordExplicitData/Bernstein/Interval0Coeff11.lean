import GafniTao.FordExplicitData.Bernstein.Interval0Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapBernsteinSourceCoeff0_88 :
    polynomialBernsteinCoeff 88 fordGapAffineSource0 88 =
      fordGapBernsteinCoeff0 88 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff0, fordGapBernsteinCoeff0]

end

end GafniTao
