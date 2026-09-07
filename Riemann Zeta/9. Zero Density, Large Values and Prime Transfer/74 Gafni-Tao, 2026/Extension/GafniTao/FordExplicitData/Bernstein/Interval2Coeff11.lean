import GafniTao.FordExplicitData.Bernstein.Interval2Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapBernsteinSourceCoeff2_88 :
    polynomialBernsteinCoeff 88 fordGapAffineSource2 88 =
      fordGapBernsteinCoeff2 88 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2, fordGapBernsteinCoeff2]

end

end GafniTao
