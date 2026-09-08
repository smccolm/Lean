import GafniTao.FordExplicitData.Bernstein.Interval6Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapBernsteinSourceCoeff6_32 :
    polynomialBernsteinCoeff 88 fordGapAffineSource6 32 =
      fordGapBernsteinCoeff6 32 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6, fordGapBernsteinCoeff6]

@[simp] theorem fordGapBernsteinSourceCoeff6_33 :
    polynomialBernsteinCoeff 88 fordGapAffineSource6 33 =
      fordGapBernsteinCoeff6 33 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6, fordGapBernsteinCoeff6]

@[simp] theorem fordGapBernsteinSourceCoeff6_34 :
    polynomialBernsteinCoeff 88 fordGapAffineSource6 34 =
      fordGapBernsteinCoeff6 34 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6, fordGapBernsteinCoeff6]

@[simp] theorem fordGapBernsteinSourceCoeff6_35 :
    polynomialBernsteinCoeff 88 fordGapAffineSource6 35 =
      fordGapBernsteinCoeff6 35 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6, fordGapBernsteinCoeff6]

@[simp] theorem fordGapBernsteinSourceCoeff6_36 :
    polynomialBernsteinCoeff 88 fordGapAffineSource6 36 =
      fordGapBernsteinCoeff6 36 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6, fordGapBernsteinCoeff6]

@[simp] theorem fordGapBernsteinSourceCoeff6_37 :
    polynomialBernsteinCoeff 88 fordGapAffineSource6 37 =
      fordGapBernsteinCoeff6 37 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6, fordGapBernsteinCoeff6]

@[simp] theorem fordGapBernsteinSourceCoeff6_38 :
    polynomialBernsteinCoeff 88 fordGapAffineSource6 38 =
      fordGapBernsteinCoeff6 38 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6, fordGapBernsteinCoeff6]

@[simp] theorem fordGapBernsteinSourceCoeff6_39 :
    polynomialBernsteinCoeff 88 fordGapAffineSource6 39 =
      fordGapBernsteinCoeff6 39 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6, fordGapBernsteinCoeff6]

end

end GafniTao
