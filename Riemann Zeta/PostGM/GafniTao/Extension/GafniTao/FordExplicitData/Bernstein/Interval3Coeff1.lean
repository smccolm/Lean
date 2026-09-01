import GafniTao.FordExplicitData.Bernstein.Interval3Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapBernsteinSourceCoeff3_8 :
    polynomialBernsteinCoeff 88 fordGapAffineSource3 8 =
      fordGapBernsteinCoeff3 8 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3, fordGapBernsteinCoeff3]

@[simp] theorem fordGapBernsteinSourceCoeff3_9 :
    polynomialBernsteinCoeff 88 fordGapAffineSource3 9 =
      fordGapBernsteinCoeff3 9 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3, fordGapBernsteinCoeff3]

@[simp] theorem fordGapBernsteinSourceCoeff3_10 :
    polynomialBernsteinCoeff 88 fordGapAffineSource3 10 =
      fordGapBernsteinCoeff3 10 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3, fordGapBernsteinCoeff3]

@[simp] theorem fordGapBernsteinSourceCoeff3_11 :
    polynomialBernsteinCoeff 88 fordGapAffineSource3 11 =
      fordGapBernsteinCoeff3 11 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3, fordGapBernsteinCoeff3]

@[simp] theorem fordGapBernsteinSourceCoeff3_12 :
    polynomialBernsteinCoeff 88 fordGapAffineSource3 12 =
      fordGapBernsteinCoeff3 12 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3, fordGapBernsteinCoeff3]

@[simp] theorem fordGapBernsteinSourceCoeff3_13 :
    polynomialBernsteinCoeff 88 fordGapAffineSource3 13 =
      fordGapBernsteinCoeff3 13 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3, fordGapBernsteinCoeff3]

@[simp] theorem fordGapBernsteinSourceCoeff3_14 :
    polynomialBernsteinCoeff 88 fordGapAffineSource3 14 =
      fordGapBernsteinCoeff3 14 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3, fordGapBernsteinCoeff3]

@[simp] theorem fordGapBernsteinSourceCoeff3_15 :
    polynomialBernsteinCoeff 88 fordGapAffineSource3 15 =
      fordGapBernsteinCoeff3 15 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3, fordGapBernsteinCoeff3]

end

end GafniTao
