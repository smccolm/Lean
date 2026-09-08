import GafniTao.FordExplicitData.Bernstein.Interval1Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapBernsteinSourceCoeff1_8 :
    polynomialBernsteinCoeff 88 fordGapAffineSource1 8 =
      fordGapBernsteinCoeff1 8 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1, fordGapBernsteinCoeff1]

@[simp] theorem fordGapBernsteinSourceCoeff1_9 :
    polynomialBernsteinCoeff 88 fordGapAffineSource1 9 =
      fordGapBernsteinCoeff1 9 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1, fordGapBernsteinCoeff1]

@[simp] theorem fordGapBernsteinSourceCoeff1_10 :
    polynomialBernsteinCoeff 88 fordGapAffineSource1 10 =
      fordGapBernsteinCoeff1 10 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1, fordGapBernsteinCoeff1]

@[simp] theorem fordGapBernsteinSourceCoeff1_11 :
    polynomialBernsteinCoeff 88 fordGapAffineSource1 11 =
      fordGapBernsteinCoeff1 11 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1, fordGapBernsteinCoeff1]

@[simp] theorem fordGapBernsteinSourceCoeff1_12 :
    polynomialBernsteinCoeff 88 fordGapAffineSource1 12 =
      fordGapBernsteinCoeff1 12 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1, fordGapBernsteinCoeff1]

@[simp] theorem fordGapBernsteinSourceCoeff1_13 :
    polynomialBernsteinCoeff 88 fordGapAffineSource1 13 =
      fordGapBernsteinCoeff1 13 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1, fordGapBernsteinCoeff1]

@[simp] theorem fordGapBernsteinSourceCoeff1_14 :
    polynomialBernsteinCoeff 88 fordGapAffineSource1 14 =
      fordGapBernsteinCoeff1 14 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1, fordGapBernsteinCoeff1]

@[simp] theorem fordGapBernsteinSourceCoeff1_15 :
    polynomialBernsteinCoeff 88 fordGapAffineSource1 15 =
      fordGapBernsteinCoeff1 15 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1, fordGapBernsteinCoeff1]

end

end GafniTao
