import GafniTao.FordExplicitData.Bernstein.Interval4Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapBernsteinSourceCoeff4_32 :
    polynomialBernsteinCoeff 88 fordGapAffineSource4 32 =
      fordGapBernsteinCoeff4 32 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4, fordGapBernsteinCoeff4]

@[simp] theorem fordGapBernsteinSourceCoeff4_33 :
    polynomialBernsteinCoeff 88 fordGapAffineSource4 33 =
      fordGapBernsteinCoeff4 33 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4, fordGapBernsteinCoeff4]

@[simp] theorem fordGapBernsteinSourceCoeff4_34 :
    polynomialBernsteinCoeff 88 fordGapAffineSource4 34 =
      fordGapBernsteinCoeff4 34 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4, fordGapBernsteinCoeff4]

@[simp] theorem fordGapBernsteinSourceCoeff4_35 :
    polynomialBernsteinCoeff 88 fordGapAffineSource4 35 =
      fordGapBernsteinCoeff4 35 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4, fordGapBernsteinCoeff4]

@[simp] theorem fordGapBernsteinSourceCoeff4_36 :
    polynomialBernsteinCoeff 88 fordGapAffineSource4 36 =
      fordGapBernsteinCoeff4 36 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4, fordGapBernsteinCoeff4]

@[simp] theorem fordGapBernsteinSourceCoeff4_37 :
    polynomialBernsteinCoeff 88 fordGapAffineSource4 37 =
      fordGapBernsteinCoeff4 37 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4, fordGapBernsteinCoeff4]

@[simp] theorem fordGapBernsteinSourceCoeff4_38 :
    polynomialBernsteinCoeff 88 fordGapAffineSource4 38 =
      fordGapBernsteinCoeff4 38 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4, fordGapBernsteinCoeff4]

@[simp] theorem fordGapBernsteinSourceCoeff4_39 :
    polynomialBernsteinCoeff 88 fordGapAffineSource4 39 =
      fordGapBernsteinCoeff4 39 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4, fordGapBernsteinCoeff4]

end

end GafniTao
