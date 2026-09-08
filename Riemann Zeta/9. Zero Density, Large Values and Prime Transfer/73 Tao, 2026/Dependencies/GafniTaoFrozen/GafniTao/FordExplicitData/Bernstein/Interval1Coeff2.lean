import GafniTao.FordExplicitData.Bernstein.Interval1Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapBernsteinSourceCoeff1_16 :
    polynomialBernsteinCoeff 88 fordGapAffineSource1 16 =
      fordGapBernsteinCoeff1 16 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1, fordGapBernsteinCoeff1]

@[simp] theorem fordGapBernsteinSourceCoeff1_17 :
    polynomialBernsteinCoeff 88 fordGapAffineSource1 17 =
      fordGapBernsteinCoeff1 17 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1, fordGapBernsteinCoeff1]

@[simp] theorem fordGapBernsteinSourceCoeff1_18 :
    polynomialBernsteinCoeff 88 fordGapAffineSource1 18 =
      fordGapBernsteinCoeff1 18 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1, fordGapBernsteinCoeff1]

@[simp] theorem fordGapBernsteinSourceCoeff1_19 :
    polynomialBernsteinCoeff 88 fordGapAffineSource1 19 =
      fordGapBernsteinCoeff1 19 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1, fordGapBernsteinCoeff1]

@[simp] theorem fordGapBernsteinSourceCoeff1_20 :
    polynomialBernsteinCoeff 88 fordGapAffineSource1 20 =
      fordGapBernsteinCoeff1 20 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1, fordGapBernsteinCoeff1]

@[simp] theorem fordGapBernsteinSourceCoeff1_21 :
    polynomialBernsteinCoeff 88 fordGapAffineSource1 21 =
      fordGapBernsteinCoeff1 21 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1, fordGapBernsteinCoeff1]

@[simp] theorem fordGapBernsteinSourceCoeff1_22 :
    polynomialBernsteinCoeff 88 fordGapAffineSource1 22 =
      fordGapBernsteinCoeff1 22 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1, fordGapBernsteinCoeff1]

@[simp] theorem fordGapBernsteinSourceCoeff1_23 :
    polynomialBernsteinCoeff 88 fordGapAffineSource1 23 =
      fordGapBernsteinCoeff1 23 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1, fordGapBernsteinCoeff1]

end

end GafniTao
