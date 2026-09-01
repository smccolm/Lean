import GafniTao.FordExplicitData.Bernstein.Interval4Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapBernsteinSourceCoeff4_8 :
    polynomialBernsteinCoeff 88 fordGapAffineSource4 8 =
      fordGapBernsteinCoeff4 8 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4, fordGapBernsteinCoeff4]

@[simp] theorem fordGapBernsteinSourceCoeff4_9 :
    polynomialBernsteinCoeff 88 fordGapAffineSource4 9 =
      fordGapBernsteinCoeff4 9 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4, fordGapBernsteinCoeff4]

@[simp] theorem fordGapBernsteinSourceCoeff4_10 :
    polynomialBernsteinCoeff 88 fordGapAffineSource4 10 =
      fordGapBernsteinCoeff4 10 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4, fordGapBernsteinCoeff4]

@[simp] theorem fordGapBernsteinSourceCoeff4_11 :
    polynomialBernsteinCoeff 88 fordGapAffineSource4 11 =
      fordGapBernsteinCoeff4 11 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4, fordGapBernsteinCoeff4]

@[simp] theorem fordGapBernsteinSourceCoeff4_12 :
    polynomialBernsteinCoeff 88 fordGapAffineSource4 12 =
      fordGapBernsteinCoeff4 12 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4, fordGapBernsteinCoeff4]

@[simp] theorem fordGapBernsteinSourceCoeff4_13 :
    polynomialBernsteinCoeff 88 fordGapAffineSource4 13 =
      fordGapBernsteinCoeff4 13 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4, fordGapBernsteinCoeff4]

@[simp] theorem fordGapBernsteinSourceCoeff4_14 :
    polynomialBernsteinCoeff 88 fordGapAffineSource4 14 =
      fordGapBernsteinCoeff4 14 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4, fordGapBernsteinCoeff4]

@[simp] theorem fordGapBernsteinSourceCoeff4_15 :
    polynomialBernsteinCoeff 88 fordGapAffineSource4 15 =
      fordGapBernsteinCoeff4 15 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4, fordGapBernsteinCoeff4]

end

end GafniTao
