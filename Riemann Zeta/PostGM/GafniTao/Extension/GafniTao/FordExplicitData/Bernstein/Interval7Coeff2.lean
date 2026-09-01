import GafniTao.FordExplicitData.Bernstein.Interval7Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapBernsteinSourceCoeff7_16 :
    polynomialBernsteinCoeff 88 fordGapAffineSource7 16 =
      fordGapBernsteinCoeff7 16 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7, fordGapBernsteinCoeff7]

@[simp] theorem fordGapBernsteinSourceCoeff7_17 :
    polynomialBernsteinCoeff 88 fordGapAffineSource7 17 =
      fordGapBernsteinCoeff7 17 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7, fordGapBernsteinCoeff7]

@[simp] theorem fordGapBernsteinSourceCoeff7_18 :
    polynomialBernsteinCoeff 88 fordGapAffineSource7 18 =
      fordGapBernsteinCoeff7 18 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7, fordGapBernsteinCoeff7]

@[simp] theorem fordGapBernsteinSourceCoeff7_19 :
    polynomialBernsteinCoeff 88 fordGapAffineSource7 19 =
      fordGapBernsteinCoeff7 19 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7, fordGapBernsteinCoeff7]

@[simp] theorem fordGapBernsteinSourceCoeff7_20 :
    polynomialBernsteinCoeff 88 fordGapAffineSource7 20 =
      fordGapBernsteinCoeff7 20 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7, fordGapBernsteinCoeff7]

@[simp] theorem fordGapBernsteinSourceCoeff7_21 :
    polynomialBernsteinCoeff 88 fordGapAffineSource7 21 =
      fordGapBernsteinCoeff7 21 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7, fordGapBernsteinCoeff7]

@[simp] theorem fordGapBernsteinSourceCoeff7_22 :
    polynomialBernsteinCoeff 88 fordGapAffineSource7 22 =
      fordGapBernsteinCoeff7 22 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7, fordGapBernsteinCoeff7]

@[simp] theorem fordGapBernsteinSourceCoeff7_23 :
    polynomialBernsteinCoeff 88 fordGapAffineSource7 23 =
      fordGapBernsteinCoeff7 23 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7, fordGapBernsteinCoeff7]

end

end GafniTao
