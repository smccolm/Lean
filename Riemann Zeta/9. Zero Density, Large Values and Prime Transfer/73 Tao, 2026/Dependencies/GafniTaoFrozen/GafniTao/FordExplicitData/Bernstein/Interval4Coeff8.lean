import GafniTao.FordExplicitData.Bernstein.Interval4Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapBernsteinSourceCoeff4_64 :
    polynomialBernsteinCoeff 88 fordGapAffineSource4 64 =
      fordGapBernsteinCoeff4 64 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4, fordGapBernsteinCoeff4]

@[simp] theorem fordGapBernsteinSourceCoeff4_65 :
    polynomialBernsteinCoeff 88 fordGapAffineSource4 65 =
      fordGapBernsteinCoeff4 65 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4, fordGapBernsteinCoeff4]

@[simp] theorem fordGapBernsteinSourceCoeff4_66 :
    polynomialBernsteinCoeff 88 fordGapAffineSource4 66 =
      fordGapBernsteinCoeff4 66 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4, fordGapBernsteinCoeff4]

@[simp] theorem fordGapBernsteinSourceCoeff4_67 :
    polynomialBernsteinCoeff 88 fordGapAffineSource4 67 =
      fordGapBernsteinCoeff4 67 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4, fordGapBernsteinCoeff4]

@[simp] theorem fordGapBernsteinSourceCoeff4_68 :
    polynomialBernsteinCoeff 88 fordGapAffineSource4 68 =
      fordGapBernsteinCoeff4 68 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4, fordGapBernsteinCoeff4]

@[simp] theorem fordGapBernsteinSourceCoeff4_69 :
    polynomialBernsteinCoeff 88 fordGapAffineSource4 69 =
      fordGapBernsteinCoeff4 69 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4, fordGapBernsteinCoeff4]

@[simp] theorem fordGapBernsteinSourceCoeff4_70 :
    polynomialBernsteinCoeff 88 fordGapAffineSource4 70 =
      fordGapBernsteinCoeff4 70 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4, fordGapBernsteinCoeff4]

@[simp] theorem fordGapBernsteinSourceCoeff4_71 :
    polynomialBernsteinCoeff 88 fordGapAffineSource4 71 =
      fordGapBernsteinCoeff4 71 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff4, fordGapBernsteinCoeff4]

end

end GafniTao
