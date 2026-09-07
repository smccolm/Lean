import GafniTao.FordExplicitData.Bernstein.Interval4Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapBernsteinSourceCoeff4_0 :
    polynomialBernsteinCoeff 88 fordGapAffineSource4 0 =
      fordGapBernsteinCoeff4 0 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4, fordGapBernsteinCoeff4]

@[simp] theorem fordGapBernsteinSourceCoeff4_1 :
    polynomialBernsteinCoeff 88 fordGapAffineSource4 1 =
      fordGapBernsteinCoeff4 1 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4, fordGapBernsteinCoeff4]

@[simp] theorem fordGapBernsteinSourceCoeff4_2 :
    polynomialBernsteinCoeff 88 fordGapAffineSource4 2 =
      fordGapBernsteinCoeff4 2 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4, fordGapBernsteinCoeff4]

@[simp] theorem fordGapBernsteinSourceCoeff4_3 :
    polynomialBernsteinCoeff 88 fordGapAffineSource4 3 =
      fordGapBernsteinCoeff4 3 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4, fordGapBernsteinCoeff4]

@[simp] theorem fordGapBernsteinSourceCoeff4_4 :
    polynomialBernsteinCoeff 88 fordGapAffineSource4 4 =
      fordGapBernsteinCoeff4 4 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4, fordGapBernsteinCoeff4]

@[simp] theorem fordGapBernsteinSourceCoeff4_5 :
    polynomialBernsteinCoeff 88 fordGapAffineSource4 5 =
      fordGapBernsteinCoeff4 5 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4, fordGapBernsteinCoeff4]

@[simp] theorem fordGapBernsteinSourceCoeff4_6 :
    polynomialBernsteinCoeff 88 fordGapAffineSource4 6 =
      fordGapBernsteinCoeff4 6 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4, fordGapBernsteinCoeff4]

@[simp] theorem fordGapBernsteinSourceCoeff4_7 :
    polynomialBernsteinCoeff 88 fordGapAffineSource4 7 =
      fordGapBernsteinCoeff4 7 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4, fordGapBernsteinCoeff4]

end

end GafniTao
