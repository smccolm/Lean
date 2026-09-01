import GafniTao.FordExplicitData.Bernstein.Interval2Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapBernsteinSourceCoeff2_32 :
    polynomialBernsteinCoeff 88 fordGapAffineSource2 32 =
      fordGapBernsteinCoeff2 32 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2, fordGapBernsteinCoeff2]

@[simp] theorem fordGapBernsteinSourceCoeff2_33 :
    polynomialBernsteinCoeff 88 fordGapAffineSource2 33 =
      fordGapBernsteinCoeff2 33 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2, fordGapBernsteinCoeff2]

@[simp] theorem fordGapBernsteinSourceCoeff2_34 :
    polynomialBernsteinCoeff 88 fordGapAffineSource2 34 =
      fordGapBernsteinCoeff2 34 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2, fordGapBernsteinCoeff2]

@[simp] theorem fordGapBernsteinSourceCoeff2_35 :
    polynomialBernsteinCoeff 88 fordGapAffineSource2 35 =
      fordGapBernsteinCoeff2 35 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2, fordGapBernsteinCoeff2]

@[simp] theorem fordGapBernsteinSourceCoeff2_36 :
    polynomialBernsteinCoeff 88 fordGapAffineSource2 36 =
      fordGapBernsteinCoeff2 36 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2, fordGapBernsteinCoeff2]

@[simp] theorem fordGapBernsteinSourceCoeff2_37 :
    polynomialBernsteinCoeff 88 fordGapAffineSource2 37 =
      fordGapBernsteinCoeff2 37 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2, fordGapBernsteinCoeff2]

@[simp] theorem fordGapBernsteinSourceCoeff2_38 :
    polynomialBernsteinCoeff 88 fordGapAffineSource2 38 =
      fordGapBernsteinCoeff2 38 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2, fordGapBernsteinCoeff2]

@[simp] theorem fordGapBernsteinSourceCoeff2_39 :
    polynomialBernsteinCoeff 88 fordGapAffineSource2 39 =
      fordGapBernsteinCoeff2 39 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2, fordGapBernsteinCoeff2]

end

end GafniTao
