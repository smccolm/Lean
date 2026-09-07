import GafniTao.FordExplicitData.Bernstein.Interval5Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapBernsteinSourceCoeff5_64 :
    polynomialBernsteinCoeff 88 fordGapAffineSource5 64 =
      fordGapBernsteinCoeff5 64 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5, fordGapBernsteinCoeff5]

@[simp] theorem fordGapBernsteinSourceCoeff5_65 :
    polynomialBernsteinCoeff 88 fordGapAffineSource5 65 =
      fordGapBernsteinCoeff5 65 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5, fordGapBernsteinCoeff5]

@[simp] theorem fordGapBernsteinSourceCoeff5_66 :
    polynomialBernsteinCoeff 88 fordGapAffineSource5 66 =
      fordGapBernsteinCoeff5 66 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5, fordGapBernsteinCoeff5]

@[simp] theorem fordGapBernsteinSourceCoeff5_67 :
    polynomialBernsteinCoeff 88 fordGapAffineSource5 67 =
      fordGapBernsteinCoeff5 67 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5, fordGapBernsteinCoeff5]

@[simp] theorem fordGapBernsteinSourceCoeff5_68 :
    polynomialBernsteinCoeff 88 fordGapAffineSource5 68 =
      fordGapBernsteinCoeff5 68 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5, fordGapBernsteinCoeff5]

@[simp] theorem fordGapBernsteinSourceCoeff5_69 :
    polynomialBernsteinCoeff 88 fordGapAffineSource5 69 =
      fordGapBernsteinCoeff5 69 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5, fordGapBernsteinCoeff5]

@[simp] theorem fordGapBernsteinSourceCoeff5_70 :
    polynomialBernsteinCoeff 88 fordGapAffineSource5 70 =
      fordGapBernsteinCoeff5 70 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5, fordGapBernsteinCoeff5]

@[simp] theorem fordGapBernsteinSourceCoeff5_71 :
    polynomialBernsteinCoeff 88 fordGapAffineSource5 71 =
      fordGapBernsteinCoeff5 71 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff5, fordGapBernsteinCoeff5]

end

end GafniTao
