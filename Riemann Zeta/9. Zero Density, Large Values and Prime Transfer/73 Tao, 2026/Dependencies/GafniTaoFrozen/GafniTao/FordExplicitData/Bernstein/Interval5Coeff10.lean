import GafniTao.FordExplicitData.Bernstein.Interval5Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapBernsteinSourceCoeff5_80 :
    polynomialBernsteinCoeff 88 fordGapAffineSource5 80 =
      fordGapBernsteinCoeff5 80 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5, fordGapBernsteinCoeff5]

@[simp] theorem fordGapBernsteinSourceCoeff5_81 :
    polynomialBernsteinCoeff 88 fordGapAffineSource5 81 =
      fordGapBernsteinCoeff5 81 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5, fordGapBernsteinCoeff5]

@[simp] theorem fordGapBernsteinSourceCoeff5_82 :
    polynomialBernsteinCoeff 88 fordGapAffineSource5 82 =
      fordGapBernsteinCoeff5 82 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5, fordGapBernsteinCoeff5]

@[simp] theorem fordGapBernsteinSourceCoeff5_83 :
    polynomialBernsteinCoeff 88 fordGapAffineSource5 83 =
      fordGapBernsteinCoeff5 83 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5, fordGapBernsteinCoeff5]

@[simp] theorem fordGapBernsteinSourceCoeff5_84 :
    polynomialBernsteinCoeff 88 fordGapAffineSource5 84 =
      fordGapBernsteinCoeff5 84 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5, fordGapBernsteinCoeff5]

@[simp] theorem fordGapBernsteinSourceCoeff5_85 :
    polynomialBernsteinCoeff 88 fordGapAffineSource5 85 =
      fordGapBernsteinCoeff5 85 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5, fordGapBernsteinCoeff5]

@[simp] theorem fordGapBernsteinSourceCoeff5_86 :
    polynomialBernsteinCoeff 88 fordGapAffineSource5 86 =
      fordGapBernsteinCoeff5 86 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5, fordGapBernsteinCoeff5]

@[simp] theorem fordGapBernsteinSourceCoeff5_87 :
    polynomialBernsteinCoeff 88 fordGapAffineSource5 87 =
      fordGapBernsteinCoeff5 87 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5, fordGapBernsteinCoeff5]

end

end GafniTao
