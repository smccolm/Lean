import GafniTao.FordExplicitData.Bernstein.Interval3Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapBernsteinSourceCoeff3_32 :
    polynomialBernsteinCoeff 88 fordGapAffineSource3 32 =
      fordGapBernsteinCoeff3 32 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3, fordGapBernsteinCoeff3]

@[simp] theorem fordGapBernsteinSourceCoeff3_33 :
    polynomialBernsteinCoeff 88 fordGapAffineSource3 33 =
      fordGapBernsteinCoeff3 33 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3, fordGapBernsteinCoeff3]

@[simp] theorem fordGapBernsteinSourceCoeff3_34 :
    polynomialBernsteinCoeff 88 fordGapAffineSource3 34 =
      fordGapBernsteinCoeff3 34 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3, fordGapBernsteinCoeff3]

@[simp] theorem fordGapBernsteinSourceCoeff3_35 :
    polynomialBernsteinCoeff 88 fordGapAffineSource3 35 =
      fordGapBernsteinCoeff3 35 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3, fordGapBernsteinCoeff3]

@[simp] theorem fordGapBernsteinSourceCoeff3_36 :
    polynomialBernsteinCoeff 88 fordGapAffineSource3 36 =
      fordGapBernsteinCoeff3 36 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3, fordGapBernsteinCoeff3]

@[simp] theorem fordGapBernsteinSourceCoeff3_37 :
    polynomialBernsteinCoeff 88 fordGapAffineSource3 37 =
      fordGapBernsteinCoeff3 37 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3, fordGapBernsteinCoeff3]

@[simp] theorem fordGapBernsteinSourceCoeff3_38 :
    polynomialBernsteinCoeff 88 fordGapAffineSource3 38 =
      fordGapBernsteinCoeff3 38 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3, fordGapBernsteinCoeff3]

@[simp] theorem fordGapBernsteinSourceCoeff3_39 :
    polynomialBernsteinCoeff 88 fordGapAffineSource3 39 =
      fordGapBernsteinCoeff3 39 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3, fordGapBernsteinCoeff3]

end

end GafniTao
