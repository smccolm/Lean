import GafniTao.FordExplicitData.Bernstein.Interval3Data

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

@[simp] theorem fordGapBernsteinSourceCoeff3_64 :
    polynomialBernsteinCoeff 88 fordGapAffineSource3 64 =
      fordGapBernsteinCoeff3 64 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3, fordGapBernsteinCoeff3]

@[simp] theorem fordGapBernsteinSourceCoeff3_65 :
    polynomialBernsteinCoeff 88 fordGapAffineSource3 65 =
      fordGapBernsteinCoeff3 65 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3, fordGapBernsteinCoeff3]

@[simp] theorem fordGapBernsteinSourceCoeff3_66 :
    polynomialBernsteinCoeff 88 fordGapAffineSource3 66 =
      fordGapBernsteinCoeff3 66 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3, fordGapBernsteinCoeff3]

@[simp] theorem fordGapBernsteinSourceCoeff3_67 :
    polynomialBernsteinCoeff 88 fordGapAffineSource3 67 =
      fordGapBernsteinCoeff3 67 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3, fordGapBernsteinCoeff3]

@[simp] theorem fordGapBernsteinSourceCoeff3_68 :
    polynomialBernsteinCoeff 88 fordGapAffineSource3 68 =
      fordGapBernsteinCoeff3 68 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3, fordGapBernsteinCoeff3]

@[simp] theorem fordGapBernsteinSourceCoeff3_69 :
    polynomialBernsteinCoeff 88 fordGapAffineSource3 69 =
      fordGapBernsteinCoeff3 69 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3, fordGapBernsteinCoeff3]

@[simp] theorem fordGapBernsteinSourceCoeff3_70 :
    polynomialBernsteinCoeff 88 fordGapAffineSource3 70 =
      fordGapBernsteinCoeff3 70 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3, fordGapBernsteinCoeff3]

@[simp] theorem fordGapBernsteinSourceCoeff3_71 :
    polynomialBernsteinCoeff 88 fordGapAffineSource3 71 =
      fordGapBernsteinCoeff3 71 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,
    Finset.sum_range_succ, Nat.choose,
    fordGapAffineCoeff3, fordGapBernsteinCoeff3]

end

end GafniTao
