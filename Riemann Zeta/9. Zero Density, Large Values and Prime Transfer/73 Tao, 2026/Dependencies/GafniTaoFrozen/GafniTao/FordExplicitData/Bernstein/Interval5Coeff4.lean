import GafniTao.FordExplicitData.Bernstein.Interval5Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapBernsteinSourceCoeff5_32 :
    polynomialBernsteinCoeff 88 fordGapAffineSource5 32 =
      fordGapBernsteinCoeff5 32 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5, fordGapBernsteinCoeff5]

@[simp] theorem fordGapBernsteinSourceCoeff5_33 :
    polynomialBernsteinCoeff 88 fordGapAffineSource5 33 =
      fordGapBernsteinCoeff5 33 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5, fordGapBernsteinCoeff5]

@[simp] theorem fordGapBernsteinSourceCoeff5_34 :
    polynomialBernsteinCoeff 88 fordGapAffineSource5 34 =
      fordGapBernsteinCoeff5 34 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5, fordGapBernsteinCoeff5]

@[simp] theorem fordGapBernsteinSourceCoeff5_35 :
    polynomialBernsteinCoeff 88 fordGapAffineSource5 35 =
      fordGapBernsteinCoeff5 35 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5, fordGapBernsteinCoeff5]

@[simp] theorem fordGapBernsteinSourceCoeff5_36 :
    polynomialBernsteinCoeff 88 fordGapAffineSource5 36 =
      fordGapBernsteinCoeff5 36 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5, fordGapBernsteinCoeff5]

@[simp] theorem fordGapBernsteinSourceCoeff5_37 :
    polynomialBernsteinCoeff 88 fordGapAffineSource5 37 =
      fordGapBernsteinCoeff5 37 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5, fordGapBernsteinCoeff5]

@[simp] theorem fordGapBernsteinSourceCoeff5_38 :
    polynomialBernsteinCoeff 88 fordGapAffineSource5 38 =
      fordGapBernsteinCoeff5 38 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5, fordGapBernsteinCoeff5]

@[simp] theorem fordGapBernsteinSourceCoeff5_39 :
    polynomialBernsteinCoeff 88 fordGapAffineSource5 39 =
      fordGapBernsteinCoeff5 39 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5, fordGapBernsteinCoeff5]

end

end GafniTao
