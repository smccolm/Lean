import GafniTao.FordExplicitData.Bernstein.Interval1Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapBernsteinSourceCoeff1_32 :
    polynomialBernsteinCoeff 88 fordGapAffineSource1 32 =
      fordGapBernsteinCoeff1 32 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1, fordGapBernsteinCoeff1]

@[simp] theorem fordGapBernsteinSourceCoeff1_33 :
    polynomialBernsteinCoeff 88 fordGapAffineSource1 33 =
      fordGapBernsteinCoeff1 33 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1, fordGapBernsteinCoeff1]

@[simp] theorem fordGapBernsteinSourceCoeff1_34 :
    polynomialBernsteinCoeff 88 fordGapAffineSource1 34 =
      fordGapBernsteinCoeff1 34 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1, fordGapBernsteinCoeff1]

@[simp] theorem fordGapBernsteinSourceCoeff1_35 :
    polynomialBernsteinCoeff 88 fordGapAffineSource1 35 =
      fordGapBernsteinCoeff1 35 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1, fordGapBernsteinCoeff1]

@[simp] theorem fordGapBernsteinSourceCoeff1_36 :
    polynomialBernsteinCoeff 88 fordGapAffineSource1 36 =
      fordGapBernsteinCoeff1 36 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1, fordGapBernsteinCoeff1]

@[simp] theorem fordGapBernsteinSourceCoeff1_37 :
    polynomialBernsteinCoeff 88 fordGapAffineSource1 37 =
      fordGapBernsteinCoeff1 37 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1, fordGapBernsteinCoeff1]

@[simp] theorem fordGapBernsteinSourceCoeff1_38 :
    polynomialBernsteinCoeff 88 fordGapAffineSource1 38 =
      fordGapBernsteinCoeff1 38 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1, fordGapBernsteinCoeff1]

@[simp] theorem fordGapBernsteinSourceCoeff1_39 :
    polynomialBernsteinCoeff 88 fordGapAffineSource1 39 =
      fordGapBernsteinCoeff1 39 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1, fordGapBernsteinCoeff1]

end

end GafniTao
