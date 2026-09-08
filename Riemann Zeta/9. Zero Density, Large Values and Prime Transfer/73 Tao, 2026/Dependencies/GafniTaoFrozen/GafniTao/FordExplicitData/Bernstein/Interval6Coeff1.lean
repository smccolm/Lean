import GafniTao.FordExplicitData.Bernstein.Interval6Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapBernsteinSourceCoeff6_8 :
    polynomialBernsteinCoeff 88 fordGapAffineSource6 8 =
      fordGapBernsteinCoeff6 8 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6, fordGapBernsteinCoeff6]

@[simp] theorem fordGapBernsteinSourceCoeff6_9 :
    polynomialBernsteinCoeff 88 fordGapAffineSource6 9 =
      fordGapBernsteinCoeff6 9 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6, fordGapBernsteinCoeff6]

@[simp] theorem fordGapBernsteinSourceCoeff6_10 :
    polynomialBernsteinCoeff 88 fordGapAffineSource6 10 =
      fordGapBernsteinCoeff6 10 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6, fordGapBernsteinCoeff6]

@[simp] theorem fordGapBernsteinSourceCoeff6_11 :
    polynomialBernsteinCoeff 88 fordGapAffineSource6 11 =
      fordGapBernsteinCoeff6 11 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6, fordGapBernsteinCoeff6]

@[simp] theorem fordGapBernsteinSourceCoeff6_12 :
    polynomialBernsteinCoeff 88 fordGapAffineSource6 12 =
      fordGapBernsteinCoeff6 12 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6, fordGapBernsteinCoeff6]

@[simp] theorem fordGapBernsteinSourceCoeff6_13 :
    polynomialBernsteinCoeff 88 fordGapAffineSource6 13 =
      fordGapBernsteinCoeff6 13 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6, fordGapBernsteinCoeff6]

@[simp] theorem fordGapBernsteinSourceCoeff6_14 :
    polynomialBernsteinCoeff 88 fordGapAffineSource6 14 =
      fordGapBernsteinCoeff6 14 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6, fordGapBernsteinCoeff6]

@[simp] theorem fordGapBernsteinSourceCoeff6_15 :
    polynomialBernsteinCoeff 88 fordGapAffineSource6 15 =
      fordGapBernsteinCoeff6 15 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6, fordGapBernsteinCoeff6]

end

end GafniTao
