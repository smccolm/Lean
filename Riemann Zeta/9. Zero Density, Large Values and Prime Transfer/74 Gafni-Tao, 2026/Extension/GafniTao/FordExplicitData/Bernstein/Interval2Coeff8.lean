import GafniTao.FordExplicitData.Bernstein.Interval2Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapBernsteinSourceCoeff2_64 :
    polynomialBernsteinCoeff 88 fordGapAffineSource2 64 =
      fordGapBernsteinCoeff2 64 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2, fordGapBernsteinCoeff2]

@[simp] theorem fordGapBernsteinSourceCoeff2_65 :
    polynomialBernsteinCoeff 88 fordGapAffineSource2 65 =
      fordGapBernsteinCoeff2 65 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2, fordGapBernsteinCoeff2]

@[simp] theorem fordGapBernsteinSourceCoeff2_66 :
    polynomialBernsteinCoeff 88 fordGapAffineSource2 66 =
      fordGapBernsteinCoeff2 66 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2, fordGapBernsteinCoeff2]

@[simp] theorem fordGapBernsteinSourceCoeff2_67 :
    polynomialBernsteinCoeff 88 fordGapAffineSource2 67 =
      fordGapBernsteinCoeff2 67 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2, fordGapBernsteinCoeff2]

@[simp] theorem fordGapBernsteinSourceCoeff2_68 :
    polynomialBernsteinCoeff 88 fordGapAffineSource2 68 =
      fordGapBernsteinCoeff2 68 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2, fordGapBernsteinCoeff2]

@[simp] theorem fordGapBernsteinSourceCoeff2_69 :
    polynomialBernsteinCoeff 88 fordGapAffineSource2 69 =
      fordGapBernsteinCoeff2 69 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2, fordGapBernsteinCoeff2]

@[simp] theorem fordGapBernsteinSourceCoeff2_70 :
    polynomialBernsteinCoeff 88 fordGapAffineSource2 70 =
      fordGapBernsteinCoeff2 70 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2, fordGapBernsteinCoeff2]

@[simp] theorem fordGapBernsteinSourceCoeff2_71 :
    polynomialBernsteinCoeff 88 fordGapAffineSource2 71 =
      fordGapBernsteinCoeff2 71 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff2, fordGapBernsteinCoeff2]

end

end GafniTao
