import GafniTao.FordExplicitData.Bernstein.Interval6Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapBernsteinSourceCoeff6_24 :
    polynomialBernsteinCoeff 88 fordGapAffineSource6 24 =
      fordGapBernsteinCoeff6 24 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6, fordGapBernsteinCoeff6]

@[simp] theorem fordGapBernsteinSourceCoeff6_25 :
    polynomialBernsteinCoeff 88 fordGapAffineSource6 25 =
      fordGapBernsteinCoeff6 25 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6, fordGapBernsteinCoeff6]

@[simp] theorem fordGapBernsteinSourceCoeff6_26 :
    polynomialBernsteinCoeff 88 fordGapAffineSource6 26 =
      fordGapBernsteinCoeff6 26 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6, fordGapBernsteinCoeff6]

@[simp] theorem fordGapBernsteinSourceCoeff6_27 :
    polynomialBernsteinCoeff 88 fordGapAffineSource6 27 =
      fordGapBernsteinCoeff6 27 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6, fordGapBernsteinCoeff6]

@[simp] theorem fordGapBernsteinSourceCoeff6_28 :
    polynomialBernsteinCoeff 88 fordGapAffineSource6 28 =
      fordGapBernsteinCoeff6 28 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6, fordGapBernsteinCoeff6]

@[simp] theorem fordGapBernsteinSourceCoeff6_29 :
    polynomialBernsteinCoeff 88 fordGapAffineSource6 29 =
      fordGapBernsteinCoeff6 29 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6, fordGapBernsteinCoeff6]

@[simp] theorem fordGapBernsteinSourceCoeff6_30 :
    polynomialBernsteinCoeff 88 fordGapAffineSource6 30 =
      fordGapBernsteinCoeff6 30 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6, fordGapBernsteinCoeff6]

@[simp] theorem fordGapBernsteinSourceCoeff6_31 :
    polynomialBernsteinCoeff 88 fordGapAffineSource6 31 =
      fordGapBernsteinCoeff6 31 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6, fordGapBernsteinCoeff6]

end

end GafniTao
