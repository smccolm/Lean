import GafniTao.FordExplicitData.Bernstein.Interval4Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapBernsteinSourceCoeff4_16 :
    polynomialBernsteinCoeff 88 fordGapAffineSource4 16 =
      fordGapBernsteinCoeff4 16 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4, fordGapBernsteinCoeff4]

@[simp] theorem fordGapBernsteinSourceCoeff4_17 :
    polynomialBernsteinCoeff 88 fordGapAffineSource4 17 =
      fordGapBernsteinCoeff4 17 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4, fordGapBernsteinCoeff4]

@[simp] theorem fordGapBernsteinSourceCoeff4_18 :
    polynomialBernsteinCoeff 88 fordGapAffineSource4 18 =
      fordGapBernsteinCoeff4 18 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4, fordGapBernsteinCoeff4]

@[simp] theorem fordGapBernsteinSourceCoeff4_19 :
    polynomialBernsteinCoeff 88 fordGapAffineSource4 19 =
      fordGapBernsteinCoeff4 19 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4, fordGapBernsteinCoeff4]

@[simp] theorem fordGapBernsteinSourceCoeff4_20 :
    polynomialBernsteinCoeff 88 fordGapAffineSource4 20 =
      fordGapBernsteinCoeff4 20 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4, fordGapBernsteinCoeff4]

@[simp] theorem fordGapBernsteinSourceCoeff4_21 :
    polynomialBernsteinCoeff 88 fordGapAffineSource4 21 =
      fordGapBernsteinCoeff4 21 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4, fordGapBernsteinCoeff4]

@[simp] theorem fordGapBernsteinSourceCoeff4_22 :
    polynomialBernsteinCoeff 88 fordGapAffineSource4 22 =
      fordGapBernsteinCoeff4 22 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4, fordGapBernsteinCoeff4]

@[simp] theorem fordGapBernsteinSourceCoeff4_23 :
    polynomialBernsteinCoeff 88 fordGapAffineSource4 23 =
      fordGapBernsteinCoeff4 23 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4, fordGapBernsteinCoeff4]

end

end GafniTao
