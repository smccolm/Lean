import GafniTao.FordExplicitData.Bernstein.Interval1Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapBernsteinSourceCoeff1_0 :
    polynomialBernsteinCoeff 88 fordGapAffineSource1 0 =
      fordGapBernsteinCoeff1 0 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1, fordGapBernsteinCoeff1]

@[simp] theorem fordGapBernsteinSourceCoeff1_1 :
    polynomialBernsteinCoeff 88 fordGapAffineSource1 1 =
      fordGapBernsteinCoeff1 1 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1, fordGapBernsteinCoeff1]

@[simp] theorem fordGapBernsteinSourceCoeff1_2 :
    polynomialBernsteinCoeff 88 fordGapAffineSource1 2 =
      fordGapBernsteinCoeff1 2 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1, fordGapBernsteinCoeff1]

@[simp] theorem fordGapBernsteinSourceCoeff1_3 :
    polynomialBernsteinCoeff 88 fordGapAffineSource1 3 =
      fordGapBernsteinCoeff1 3 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1, fordGapBernsteinCoeff1]

@[simp] theorem fordGapBernsteinSourceCoeff1_4 :
    polynomialBernsteinCoeff 88 fordGapAffineSource1 4 =
      fordGapBernsteinCoeff1 4 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1, fordGapBernsteinCoeff1]

@[simp] theorem fordGapBernsteinSourceCoeff1_5 :
    polynomialBernsteinCoeff 88 fordGapAffineSource1 5 =
      fordGapBernsteinCoeff1 5 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1, fordGapBernsteinCoeff1]

@[simp] theorem fordGapBernsteinSourceCoeff1_6 :
    polynomialBernsteinCoeff 88 fordGapAffineSource1 6 =
      fordGapBernsteinCoeff1 6 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1, fordGapBernsteinCoeff1]

@[simp] theorem fordGapBernsteinSourceCoeff1_7 :
    polynomialBernsteinCoeff 88 fordGapAffineSource1 7 =
      fordGapBernsteinCoeff1 7 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1, fordGapBernsteinCoeff1]

end

end GafniTao
