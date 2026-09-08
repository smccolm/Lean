import GafniTao.FordExplicitData.Bernstein.Interval2Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapBernsteinSourceCoeff2_16 :
    polynomialBernsteinCoeff 88 fordGapAffineSource2 16 =
      fordGapBernsteinCoeff2 16 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2, fordGapBernsteinCoeff2]

@[simp] theorem fordGapBernsteinSourceCoeff2_17 :
    polynomialBernsteinCoeff 88 fordGapAffineSource2 17 =
      fordGapBernsteinCoeff2 17 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2, fordGapBernsteinCoeff2]

@[simp] theorem fordGapBernsteinSourceCoeff2_18 :
    polynomialBernsteinCoeff 88 fordGapAffineSource2 18 =
      fordGapBernsteinCoeff2 18 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2, fordGapBernsteinCoeff2]

@[simp] theorem fordGapBernsteinSourceCoeff2_19 :
    polynomialBernsteinCoeff 88 fordGapAffineSource2 19 =
      fordGapBernsteinCoeff2 19 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2, fordGapBernsteinCoeff2]

@[simp] theorem fordGapBernsteinSourceCoeff2_20 :
    polynomialBernsteinCoeff 88 fordGapAffineSource2 20 =
      fordGapBernsteinCoeff2 20 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2, fordGapBernsteinCoeff2]

@[simp] theorem fordGapBernsteinSourceCoeff2_21 :
    polynomialBernsteinCoeff 88 fordGapAffineSource2 21 =
      fordGapBernsteinCoeff2 21 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2, fordGapBernsteinCoeff2]

@[simp] theorem fordGapBernsteinSourceCoeff2_22 :
    polynomialBernsteinCoeff 88 fordGapAffineSource2 22 =
      fordGapBernsteinCoeff2 22 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2, fordGapBernsteinCoeff2]

@[simp] theorem fordGapBernsteinSourceCoeff2_23 :
    polynomialBernsteinCoeff 88 fordGapAffineSource2 23 =
      fordGapBernsteinCoeff2 23 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2, fordGapBernsteinCoeff2]

end

end GafniTao
