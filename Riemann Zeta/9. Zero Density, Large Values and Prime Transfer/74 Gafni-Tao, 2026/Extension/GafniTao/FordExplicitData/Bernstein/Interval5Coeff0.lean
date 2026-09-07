import GafniTao.FordExplicitData.Bernstein.Interval5Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapBernsteinSourceCoeff5_0 :
    polynomialBernsteinCoeff 88 fordGapAffineSource5 0 =
      fordGapBernsteinCoeff5 0 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5, fordGapBernsteinCoeff5]

@[simp] theorem fordGapBernsteinSourceCoeff5_1 :
    polynomialBernsteinCoeff 88 fordGapAffineSource5 1 =
      fordGapBernsteinCoeff5 1 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5, fordGapBernsteinCoeff5]

@[simp] theorem fordGapBernsteinSourceCoeff5_2 :
    polynomialBernsteinCoeff 88 fordGapAffineSource5 2 =
      fordGapBernsteinCoeff5 2 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5, fordGapBernsteinCoeff5]

@[simp] theorem fordGapBernsteinSourceCoeff5_3 :
    polynomialBernsteinCoeff 88 fordGapAffineSource5 3 =
      fordGapBernsteinCoeff5 3 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5, fordGapBernsteinCoeff5]

@[simp] theorem fordGapBernsteinSourceCoeff5_4 :
    polynomialBernsteinCoeff 88 fordGapAffineSource5 4 =
      fordGapBernsteinCoeff5 4 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5, fordGapBernsteinCoeff5]

@[simp] theorem fordGapBernsteinSourceCoeff5_5 :
    polynomialBernsteinCoeff 88 fordGapAffineSource5 5 =
      fordGapBernsteinCoeff5 5 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5, fordGapBernsteinCoeff5]

@[simp] theorem fordGapBernsteinSourceCoeff5_6 :
    polynomialBernsteinCoeff 88 fordGapAffineSource5 6 =
      fordGapBernsteinCoeff5 6 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5, fordGapBernsteinCoeff5]

@[simp] theorem fordGapBernsteinSourceCoeff5_7 :
    polynomialBernsteinCoeff 88 fordGapAffineSource5 7 =
      fordGapBernsteinCoeff5 7 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5, fordGapBernsteinCoeff5]

end

end GafniTao
