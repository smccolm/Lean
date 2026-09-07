import GafniTao.FordExplicitData.Bernstein.Interval1Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapBernsteinSourceCoeff1_88 :
    polynomialBernsteinCoeff 88 fordGapAffineSource1 88 =
      fordGapBernsteinCoeff1 88 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1, fordGapBernsteinCoeff1]

end

end GafniTao
