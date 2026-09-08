import GafniTao.FordExplicitData.Bernstein.Interval7Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapBernsteinSourceCoeff7_88 :
    polynomialBernsteinCoeff 88 fordGapAffineSource7 88 =
      fordGapBernsteinCoeff7 88 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7, fordGapBernsteinCoeff7]

end

end GafniTao
