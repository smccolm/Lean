import GafniTao.FordExplicitData.Bernstein.Interval7Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapBernsteinSourceCoeff7_8 :
    polynomialBernsteinCoeff 88 fordGapAffineSource7 8 =
      fordGapBernsteinCoeff7 8 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7, fordGapBernsteinCoeff7]

@[simp] theorem fordGapBernsteinSourceCoeff7_9 :
    polynomialBernsteinCoeff 88 fordGapAffineSource7 9 =
      fordGapBernsteinCoeff7 9 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7, fordGapBernsteinCoeff7]

@[simp] theorem fordGapBernsteinSourceCoeff7_10 :
    polynomialBernsteinCoeff 88 fordGapAffineSource7 10 =
      fordGapBernsteinCoeff7 10 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7, fordGapBernsteinCoeff7]

@[simp] theorem fordGapBernsteinSourceCoeff7_11 :
    polynomialBernsteinCoeff 88 fordGapAffineSource7 11 =
      fordGapBernsteinCoeff7 11 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7, fordGapBernsteinCoeff7]

@[simp] theorem fordGapBernsteinSourceCoeff7_12 :
    polynomialBernsteinCoeff 88 fordGapAffineSource7 12 =
      fordGapBernsteinCoeff7 12 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7, fordGapBernsteinCoeff7]

@[simp] theorem fordGapBernsteinSourceCoeff7_13 :
    polynomialBernsteinCoeff 88 fordGapAffineSource7 13 =
      fordGapBernsteinCoeff7 13 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7, fordGapBernsteinCoeff7]

@[simp] theorem fordGapBernsteinSourceCoeff7_14 :
    polynomialBernsteinCoeff 88 fordGapAffineSource7 14 =
      fordGapBernsteinCoeff7 14 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7, fordGapBernsteinCoeff7]

@[simp] theorem fordGapBernsteinSourceCoeff7_15 :
    polynomialBernsteinCoeff 88 fordGapAffineSource7 15 =
      fordGapBernsteinCoeff7 15 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7, fordGapBernsteinCoeff7]

end

end GafniTao
