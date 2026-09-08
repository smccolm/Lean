import GafniTao.FordExplicitData.Bernstein.Interval5Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapBernsteinSourceCoeff5_8 :
    polynomialBernsteinCoeff 88 fordGapAffineSource5 8 =
      fordGapBernsteinCoeff5 8 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5, fordGapBernsteinCoeff5]

@[simp] theorem fordGapBernsteinSourceCoeff5_9 :
    polynomialBernsteinCoeff 88 fordGapAffineSource5 9 =
      fordGapBernsteinCoeff5 9 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5, fordGapBernsteinCoeff5]

@[simp] theorem fordGapBernsteinSourceCoeff5_10 :
    polynomialBernsteinCoeff 88 fordGapAffineSource5 10 =
      fordGapBernsteinCoeff5 10 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5, fordGapBernsteinCoeff5]

@[simp] theorem fordGapBernsteinSourceCoeff5_11 :
    polynomialBernsteinCoeff 88 fordGapAffineSource5 11 =
      fordGapBernsteinCoeff5 11 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5, fordGapBernsteinCoeff5]

@[simp] theorem fordGapBernsteinSourceCoeff5_12 :
    polynomialBernsteinCoeff 88 fordGapAffineSource5 12 =
      fordGapBernsteinCoeff5 12 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5, fordGapBernsteinCoeff5]

@[simp] theorem fordGapBernsteinSourceCoeff5_13 :
    polynomialBernsteinCoeff 88 fordGapAffineSource5 13 =
      fordGapBernsteinCoeff5 13 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5, fordGapBernsteinCoeff5]

@[simp] theorem fordGapBernsteinSourceCoeff5_14 :
    polynomialBernsteinCoeff 88 fordGapAffineSource5 14 =
      fordGapBernsteinCoeff5 14 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5, fordGapBernsteinCoeff5]

@[simp] theorem fordGapBernsteinSourceCoeff5_15 :
    polynomialBernsteinCoeff 88 fordGapAffineSource5 15 =
      fordGapBernsteinCoeff5 15 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5, fordGapBernsteinCoeff5]

end

end GafniTao
