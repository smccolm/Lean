import GafniTao.FordExplicitData.Bernstein.Interval1Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapBernsteinSourceCoeff1_64 :
    polynomialBernsteinCoeff 88 fordGapAffineSource1 64 =
      fordGapBernsteinCoeff1 64 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1, fordGapBernsteinCoeff1]

@[simp] theorem fordGapBernsteinSourceCoeff1_65 :
    polynomialBernsteinCoeff 88 fordGapAffineSource1 65 =
      fordGapBernsteinCoeff1 65 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1, fordGapBernsteinCoeff1]

@[simp] theorem fordGapBernsteinSourceCoeff1_66 :
    polynomialBernsteinCoeff 88 fordGapAffineSource1 66 =
      fordGapBernsteinCoeff1 66 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1, fordGapBernsteinCoeff1]

@[simp] theorem fordGapBernsteinSourceCoeff1_67 :
    polynomialBernsteinCoeff 88 fordGapAffineSource1 67 =
      fordGapBernsteinCoeff1 67 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1, fordGapBernsteinCoeff1]

@[simp] theorem fordGapBernsteinSourceCoeff1_68 :
    polynomialBernsteinCoeff 88 fordGapAffineSource1 68 =
      fordGapBernsteinCoeff1 68 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1, fordGapBernsteinCoeff1]

@[simp] theorem fordGapBernsteinSourceCoeff1_69 :
    polynomialBernsteinCoeff 88 fordGapAffineSource1 69 =
      fordGapBernsteinCoeff1 69 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1, fordGapBernsteinCoeff1]

@[simp] theorem fordGapBernsteinSourceCoeff1_70 :
    polynomialBernsteinCoeff 88 fordGapAffineSource1 70 =
      fordGapBernsteinCoeff1 70 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1, fordGapBernsteinCoeff1]

@[simp] theorem fordGapBernsteinSourceCoeff1_71 :
    polynomialBernsteinCoeff 88 fordGapAffineSource1 71 =
      fordGapBernsteinCoeff1 71 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff1, fordGapBernsteinCoeff1]

end

end GafniTao
