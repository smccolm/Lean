import GafniTao.FordBernsteinBasis
import GafniTao.FordGapExplicitIdentity

namespace GafniTao

noncomputable section

open Polynomial
open scoped Polynomial

example : fordNumericalGapExplicit.natDegree ≤ 88 := by
  compute_degree

def probeAffine1 : ℚ[X] :=
  fordNumericalGapExplicit.comp
    (Polynomial.C (11 / 80 : ℚ) + Polynomial.C (11 / 80 : ℚ) * Polynomial.X)

example : 0 ≤ polynomialBernsteinCoeff 88 probeAffine1 0 := by
  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff, probeAffine1,
    Finset.sum_range_succ, fordNumericalGapExplicit,
    fordNumericalGapValueBlock0, fordNumericalGapValueBlock1,
    fordNumericalGapValueBlock2, fordNumericalGapValueBlock3,
    fordNumericalGapValueBlock4, fordNumericalGapValueBlock5,
    fordNumericalGapValueBlock6, fordNumericalGapValueBlock7,
    Polynomial.comp_eq_sum_left, Polynomial.sum, Nat.choose]

end

end GafniTao
