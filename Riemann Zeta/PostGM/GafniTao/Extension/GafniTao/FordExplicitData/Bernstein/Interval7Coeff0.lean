import GafniTao.FordExplicitData.Bernstein.Interval7Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapBernsteinSourceCoeff7_0 :
    polynomialBernsteinCoeff 88 fordGapAffineSource7 0 =
      fordGapBernsteinCoeff7 0 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7, fordGapBernsteinCoeff7]

@[simp] theorem fordGapBernsteinSourceCoeff7_1 :
    polynomialBernsteinCoeff 88 fordGapAffineSource7 1 =
      fordGapBernsteinCoeff7 1 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7, fordGapBernsteinCoeff7]

@[simp] theorem fordGapBernsteinSourceCoeff7_2 :
    polynomialBernsteinCoeff 88 fordGapAffineSource7 2 =
      fordGapBernsteinCoeff7 2 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7, fordGapBernsteinCoeff7]

@[simp] theorem fordGapBernsteinSourceCoeff7_3 :
    polynomialBernsteinCoeff 88 fordGapAffineSource7 3 =
      fordGapBernsteinCoeff7 3 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7, fordGapBernsteinCoeff7]

@[simp] theorem fordGapBernsteinSourceCoeff7_4 :
    polynomialBernsteinCoeff 88 fordGapAffineSource7 4 =
      fordGapBernsteinCoeff7 4 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7, fordGapBernsteinCoeff7]

@[simp] theorem fordGapBernsteinSourceCoeff7_5 :
    polynomialBernsteinCoeff 88 fordGapAffineSource7 5 =
      fordGapBernsteinCoeff7 5 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7, fordGapBernsteinCoeff7]

@[simp] theorem fordGapBernsteinSourceCoeff7_6 :
    polynomialBernsteinCoeff 88 fordGapAffineSource7 6 =
      fordGapBernsteinCoeff7 6 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7, fordGapBernsteinCoeff7]

@[simp] theorem fordGapBernsteinSourceCoeff7_7 :
    polynomialBernsteinCoeff 88 fordGapAffineSource7 7 =
      fordGapBernsteinCoeff7 7 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7, fordGapBernsteinCoeff7]

end

end GafniTao
