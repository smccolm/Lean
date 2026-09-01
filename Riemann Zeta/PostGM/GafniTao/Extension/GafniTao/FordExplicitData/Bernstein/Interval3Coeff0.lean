import GafniTao.FordExplicitData.Bernstein.Interval3Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapBernsteinSourceCoeff3_0 :
    polynomialBernsteinCoeff 88 fordGapAffineSource3 0 =
      fordGapBernsteinCoeff3 0 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3, fordGapBernsteinCoeff3]

@[simp] theorem fordGapBernsteinSourceCoeff3_1 :
    polynomialBernsteinCoeff 88 fordGapAffineSource3 1 =
      fordGapBernsteinCoeff3 1 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3, fordGapBernsteinCoeff3]

@[simp] theorem fordGapBernsteinSourceCoeff3_2 :
    polynomialBernsteinCoeff 88 fordGapAffineSource3 2 =
      fordGapBernsteinCoeff3 2 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3, fordGapBernsteinCoeff3]

@[simp] theorem fordGapBernsteinSourceCoeff3_3 :
    polynomialBernsteinCoeff 88 fordGapAffineSource3 3 =
      fordGapBernsteinCoeff3 3 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3, fordGapBernsteinCoeff3]

@[simp] theorem fordGapBernsteinSourceCoeff3_4 :
    polynomialBernsteinCoeff 88 fordGapAffineSource3 4 =
      fordGapBernsteinCoeff3 4 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3, fordGapBernsteinCoeff3]

@[simp] theorem fordGapBernsteinSourceCoeff3_5 :
    polynomialBernsteinCoeff 88 fordGapAffineSource3 5 =
      fordGapBernsteinCoeff3 5 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3, fordGapBernsteinCoeff3]

@[simp] theorem fordGapBernsteinSourceCoeff3_6 :
    polynomialBernsteinCoeff 88 fordGapAffineSource3 6 =
      fordGapBernsteinCoeff3 6 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3, fordGapBernsteinCoeff3]

@[simp] theorem fordGapBernsteinSourceCoeff3_7 :
    polynomialBernsteinCoeff 88 fordGapAffineSource3 7 =
      fordGapBernsteinCoeff3 7 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3, fordGapBernsteinCoeff3]

end

end GafniTao
