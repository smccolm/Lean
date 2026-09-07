import GafniTao.FordExplicitData.Bernstein.Interval2Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapBernsteinSourceCoeff2_0 :
    polynomialBernsteinCoeff 88 fordGapAffineSource2 0 =
      fordGapBernsteinCoeff2 0 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2, fordGapBernsteinCoeff2]

@[simp] theorem fordGapBernsteinSourceCoeff2_1 :
    polynomialBernsteinCoeff 88 fordGapAffineSource2 1 =
      fordGapBernsteinCoeff2 1 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2, fordGapBernsteinCoeff2]

@[simp] theorem fordGapBernsteinSourceCoeff2_2 :
    polynomialBernsteinCoeff 88 fordGapAffineSource2 2 =
      fordGapBernsteinCoeff2 2 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2, fordGapBernsteinCoeff2]

@[simp] theorem fordGapBernsteinSourceCoeff2_3 :
    polynomialBernsteinCoeff 88 fordGapAffineSource2 3 =
      fordGapBernsteinCoeff2 3 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2, fordGapBernsteinCoeff2]

@[simp] theorem fordGapBernsteinSourceCoeff2_4 :
    polynomialBernsteinCoeff 88 fordGapAffineSource2 4 =
      fordGapBernsteinCoeff2 4 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2, fordGapBernsteinCoeff2]

@[simp] theorem fordGapBernsteinSourceCoeff2_5 :
    polynomialBernsteinCoeff 88 fordGapAffineSource2 5 =
      fordGapBernsteinCoeff2 5 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2, fordGapBernsteinCoeff2]

@[simp] theorem fordGapBernsteinSourceCoeff2_6 :
    polynomialBernsteinCoeff 88 fordGapAffineSource2 6 =
      fordGapBernsteinCoeff2 6 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2, fordGapBernsteinCoeff2]

@[simp] theorem fordGapBernsteinSourceCoeff2_7 :
    polynomialBernsteinCoeff 88 fordGapAffineSource2 7 =
      fordGapBernsteinCoeff2 7 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2, fordGapBernsteinCoeff2]

end

end GafniTao
