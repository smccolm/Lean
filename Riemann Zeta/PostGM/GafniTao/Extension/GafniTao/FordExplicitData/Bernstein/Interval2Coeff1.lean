import GafniTao.FordExplicitData.Bernstein.Interval2Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapBernsteinSourceCoeff2_8 :
    polynomialBernsteinCoeff 88 fordGapAffineSource2 8 =
      fordGapBernsteinCoeff2 8 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2, fordGapBernsteinCoeff2]

@[simp] theorem fordGapBernsteinSourceCoeff2_9 :
    polynomialBernsteinCoeff 88 fordGapAffineSource2 9 =
      fordGapBernsteinCoeff2 9 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2, fordGapBernsteinCoeff2]

@[simp] theorem fordGapBernsteinSourceCoeff2_10 :
    polynomialBernsteinCoeff 88 fordGapAffineSource2 10 =
      fordGapBernsteinCoeff2 10 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2, fordGapBernsteinCoeff2]

@[simp] theorem fordGapBernsteinSourceCoeff2_11 :
    polynomialBernsteinCoeff 88 fordGapAffineSource2 11 =
      fordGapBernsteinCoeff2 11 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2, fordGapBernsteinCoeff2]

@[simp] theorem fordGapBernsteinSourceCoeff2_12 :
    polynomialBernsteinCoeff 88 fordGapAffineSource2 12 =
      fordGapBernsteinCoeff2 12 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2, fordGapBernsteinCoeff2]

@[simp] theorem fordGapBernsteinSourceCoeff2_13 :
    polynomialBernsteinCoeff 88 fordGapAffineSource2 13 =
      fordGapBernsteinCoeff2 13 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2, fordGapBernsteinCoeff2]

@[simp] theorem fordGapBernsteinSourceCoeff2_14 :
    polynomialBernsteinCoeff 88 fordGapAffineSource2 14 =
      fordGapBernsteinCoeff2 14 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2, fordGapBernsteinCoeff2]

@[simp] theorem fordGapBernsteinSourceCoeff2_15 :
    polynomialBernsteinCoeff 88 fordGapAffineSource2 15 =
      fordGapBernsteinCoeff2 15 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2, fordGapBernsteinCoeff2]

end

end GafniTao
