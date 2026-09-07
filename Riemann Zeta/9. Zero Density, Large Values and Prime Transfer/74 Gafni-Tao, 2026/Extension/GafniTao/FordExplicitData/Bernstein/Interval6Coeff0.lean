import GafniTao.FordExplicitData.Bernstein.Interval6Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapBernsteinSourceCoeff6_0 :
    polynomialBernsteinCoeff 88 fordGapAffineSource6 0 =
      fordGapBernsteinCoeff6 0 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6, fordGapBernsteinCoeff6]

@[simp] theorem fordGapBernsteinSourceCoeff6_1 :
    polynomialBernsteinCoeff 88 fordGapAffineSource6 1 =
      fordGapBernsteinCoeff6 1 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6, fordGapBernsteinCoeff6]

@[simp] theorem fordGapBernsteinSourceCoeff6_2 :
    polynomialBernsteinCoeff 88 fordGapAffineSource6 2 =
      fordGapBernsteinCoeff6 2 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6, fordGapBernsteinCoeff6]

@[simp] theorem fordGapBernsteinSourceCoeff6_3 :
    polynomialBernsteinCoeff 88 fordGapAffineSource6 3 =
      fordGapBernsteinCoeff6 3 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6, fordGapBernsteinCoeff6]

@[simp] theorem fordGapBernsteinSourceCoeff6_4 :
    polynomialBernsteinCoeff 88 fordGapAffineSource6 4 =
      fordGapBernsteinCoeff6 4 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6, fordGapBernsteinCoeff6]

@[simp] theorem fordGapBernsteinSourceCoeff6_5 :
    polynomialBernsteinCoeff 88 fordGapAffineSource6 5 =
      fordGapBernsteinCoeff6 5 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6, fordGapBernsteinCoeff6]

@[simp] theorem fordGapBernsteinSourceCoeff6_6 :
    polynomialBernsteinCoeff 88 fordGapAffineSource6 6 =
      fordGapBernsteinCoeff6 6 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6, fordGapBernsteinCoeff6]

@[simp] theorem fordGapBernsteinSourceCoeff6_7 :
    polynomialBernsteinCoeff 88 fordGapAffineSource6 7 =
      fordGapBernsteinCoeff6 7 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6, fordGapBernsteinCoeff6]

end

end GafniTao
