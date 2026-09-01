import GafniTao.FordExplicitData.Bernstein.Interval0Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapBernsteinSourceCoeff0_0 :
    polynomialBernsteinCoeff 88 fordGapAffineSource0 0 =
      fordGapBernsteinCoeff0 0 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff0, fordGapBernsteinCoeff0]

@[simp] theorem fordGapBernsteinSourceCoeff0_1 :
    polynomialBernsteinCoeff 88 fordGapAffineSource0 1 =
      fordGapBernsteinCoeff0 1 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff0, fordGapBernsteinCoeff0]

@[simp] theorem fordGapBernsteinSourceCoeff0_2 :
    polynomialBernsteinCoeff 88 fordGapAffineSource0 2 =
      fordGapBernsteinCoeff0 2 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff0, fordGapBernsteinCoeff0]

@[simp] theorem fordGapBernsteinSourceCoeff0_3 :
    polynomialBernsteinCoeff 88 fordGapAffineSource0 3 =
      fordGapBernsteinCoeff0 3 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff0, fordGapBernsteinCoeff0]

@[simp] theorem fordGapBernsteinSourceCoeff0_4 :
    polynomialBernsteinCoeff 88 fordGapAffineSource0 4 =
      fordGapBernsteinCoeff0 4 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff0, fordGapBernsteinCoeff0]

@[simp] theorem fordGapBernsteinSourceCoeff0_5 :
    polynomialBernsteinCoeff 88 fordGapAffineSource0 5 =
      fordGapBernsteinCoeff0 5 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff0, fordGapBernsteinCoeff0]

@[simp] theorem fordGapBernsteinSourceCoeff0_6 :
    polynomialBernsteinCoeff 88 fordGapAffineSource0 6 =
      fordGapBernsteinCoeff0 6 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff0, fordGapBernsteinCoeff0]

@[simp] theorem fordGapBernsteinSourceCoeff0_7 :
    polynomialBernsteinCoeff 88 fordGapAffineSource0 7 =
      fordGapBernsteinCoeff0 7 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff0, fordGapBernsteinCoeff0]

end

end GafniTao
