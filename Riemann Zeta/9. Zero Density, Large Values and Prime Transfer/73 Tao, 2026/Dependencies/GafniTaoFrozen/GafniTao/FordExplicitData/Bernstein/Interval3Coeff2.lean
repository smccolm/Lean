import GafniTao.FordExplicitData.Bernstein.Interval3Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapBernsteinSourceCoeff3_16 :
    polynomialBernsteinCoeff 88 fordGapAffineSource3 16 =
      fordGapBernsteinCoeff3 16 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3, fordGapBernsteinCoeff3]

@[simp] theorem fordGapBernsteinSourceCoeff3_17 :
    polynomialBernsteinCoeff 88 fordGapAffineSource3 17 =
      fordGapBernsteinCoeff3 17 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3, fordGapBernsteinCoeff3]

@[simp] theorem fordGapBernsteinSourceCoeff3_18 :
    polynomialBernsteinCoeff 88 fordGapAffineSource3 18 =
      fordGapBernsteinCoeff3 18 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3, fordGapBernsteinCoeff3]

@[simp] theorem fordGapBernsteinSourceCoeff3_19 :
    polynomialBernsteinCoeff 88 fordGapAffineSource3 19 =
      fordGapBernsteinCoeff3 19 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3, fordGapBernsteinCoeff3]

@[simp] theorem fordGapBernsteinSourceCoeff3_20 :
    polynomialBernsteinCoeff 88 fordGapAffineSource3 20 =
      fordGapBernsteinCoeff3 20 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3, fordGapBernsteinCoeff3]

@[simp] theorem fordGapBernsteinSourceCoeff3_21 :
    polynomialBernsteinCoeff 88 fordGapAffineSource3 21 =
      fordGapBernsteinCoeff3 21 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3, fordGapBernsteinCoeff3]

@[simp] theorem fordGapBernsteinSourceCoeff3_22 :
    polynomialBernsteinCoeff 88 fordGapAffineSource3 22 =
      fordGapBernsteinCoeff3 22 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3, fordGapBernsteinCoeff3]

@[simp] theorem fordGapBernsteinSourceCoeff3_23 :
    polynomialBernsteinCoeff 88 fordGapAffineSource3 23 =
      fordGapBernsteinCoeff3 23 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3, fordGapBernsteinCoeff3]

end

end GafniTao
