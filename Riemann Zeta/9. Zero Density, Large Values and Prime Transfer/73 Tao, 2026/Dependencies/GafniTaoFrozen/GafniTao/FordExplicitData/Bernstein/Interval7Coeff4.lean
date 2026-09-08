import GafniTao.FordExplicitData.Bernstein.Interval7Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapBernsteinSourceCoeff7_32 :
    polynomialBernsteinCoeff 88 fordGapAffineSource7 32 =
      fordGapBernsteinCoeff7 32 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7, fordGapBernsteinCoeff7]

@[simp] theorem fordGapBernsteinSourceCoeff7_33 :
    polynomialBernsteinCoeff 88 fordGapAffineSource7 33 =
      fordGapBernsteinCoeff7 33 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7, fordGapBernsteinCoeff7]

@[simp] theorem fordGapBernsteinSourceCoeff7_34 :
    polynomialBernsteinCoeff 88 fordGapAffineSource7 34 =
      fordGapBernsteinCoeff7 34 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7, fordGapBernsteinCoeff7]

@[simp] theorem fordGapBernsteinSourceCoeff7_35 :
    polynomialBernsteinCoeff 88 fordGapAffineSource7 35 =
      fordGapBernsteinCoeff7 35 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7, fordGapBernsteinCoeff7]

@[simp] theorem fordGapBernsteinSourceCoeff7_36 :
    polynomialBernsteinCoeff 88 fordGapAffineSource7 36 =
      fordGapBernsteinCoeff7 36 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7, fordGapBernsteinCoeff7]

@[simp] theorem fordGapBernsteinSourceCoeff7_37 :
    polynomialBernsteinCoeff 88 fordGapAffineSource7 37 =
      fordGapBernsteinCoeff7 37 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7, fordGapBernsteinCoeff7]

@[simp] theorem fordGapBernsteinSourceCoeff7_38 :
    polynomialBernsteinCoeff 88 fordGapAffineSource7 38 =
      fordGapBernsteinCoeff7 38 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7, fordGapBernsteinCoeff7]

@[simp] theorem fordGapBernsteinSourceCoeff7_39 :
    polynomialBernsteinCoeff 88 fordGapAffineSource7 39 =
      fordGapBernsteinCoeff7 39 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff7, fordGapBernsteinCoeff7]

end

end GafniTao
