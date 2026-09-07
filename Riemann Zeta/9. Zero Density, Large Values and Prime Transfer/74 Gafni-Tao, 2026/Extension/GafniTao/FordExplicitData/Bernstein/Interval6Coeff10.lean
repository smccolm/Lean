import GafniTao.FordExplicitData.Bernstein.Interval6Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapBernsteinSourceCoeff6_80 :
    polynomialBernsteinCoeff 88 fordGapAffineSource6 80 =
      fordGapBernsteinCoeff6 80 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6, fordGapBernsteinCoeff6]

@[simp] theorem fordGapBernsteinSourceCoeff6_81 :
    polynomialBernsteinCoeff 88 fordGapAffineSource6 81 =
      fordGapBernsteinCoeff6 81 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6, fordGapBernsteinCoeff6]

@[simp] theorem fordGapBernsteinSourceCoeff6_82 :
    polynomialBernsteinCoeff 88 fordGapAffineSource6 82 =
      fordGapBernsteinCoeff6 82 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6, fordGapBernsteinCoeff6]

@[simp] theorem fordGapBernsteinSourceCoeff6_83 :
    polynomialBernsteinCoeff 88 fordGapAffineSource6 83 =
      fordGapBernsteinCoeff6 83 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6, fordGapBernsteinCoeff6]

@[simp] theorem fordGapBernsteinSourceCoeff6_84 :
    polynomialBernsteinCoeff 88 fordGapAffineSource6 84 =
      fordGapBernsteinCoeff6 84 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6, fordGapBernsteinCoeff6]

@[simp] theorem fordGapBernsteinSourceCoeff6_85 :
    polynomialBernsteinCoeff 88 fordGapAffineSource6 85 =
      fordGapBernsteinCoeff6 85 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6, fordGapBernsteinCoeff6]

@[simp] theorem fordGapBernsteinSourceCoeff6_86 :
    polynomialBernsteinCoeff 88 fordGapAffineSource6 86 =
      fordGapBernsteinCoeff6 86 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6, fordGapBernsteinCoeff6]

@[simp] theorem fordGapBernsteinSourceCoeff6_87 :
    polynomialBernsteinCoeff 88 fordGapAffineSource6 87 =
      fordGapBernsteinCoeff6 87 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff6, fordGapBernsteinCoeff6]

end

end GafniTao
