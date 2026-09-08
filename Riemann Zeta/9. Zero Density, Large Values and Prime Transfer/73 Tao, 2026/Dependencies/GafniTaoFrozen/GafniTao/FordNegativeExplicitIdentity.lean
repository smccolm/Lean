import GafniTao.FordNegativeIntegralFormula
import GafniTao.FordExplicitData.NegativePrimitiveCoefficients

/-!
# Source identification of Ford's negative-side primitive

This module identifies the exact polynomial antiderivative used on the
negative compact interval with its independently generated rational
certificate.  The proof uses the source derivative identity, checks every
coefficient through degree `55`, and proves that both tails vanish.
-/

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

theorem fordBiIntegralPolynomial_fordNegativeUpper_eq_explicit :
    fordBiIntegralPolynomial fordNegativeUpperPolynomial =
      fordNegativePrimitiveExplicit := by
  rw [fordNegativeUpperPolynomial_eq_explicit]
  apply Polynomial.ext
  intro n
  cases n with
  | zero =>
      rw [fordBiIntegralPolynomial_coeff_zero]
      simp [fordNegativePrimitiveExplicit, fordNegativePrimitiveBlock0,
        fordNegativePrimitiveBlock1, fordNegativePrimitiveBlock2]
  | succ n =>
      rw [fordBiIntegralPolynomial_coeff_succ]
      by_cases hn : n < 55
      · interval_cases n <;> simp <;> norm_num
      · have hn' : 55 ≤ n := by omega
        have hupper : fordNegativeUpperExplicit.coeff n = 0 := by
          apply Polynomial.coeff_eq_zero_of_natDegree_lt
          have hdegree : fordNegativeUpperExplicit.natDegree ≤ 54 := by
            unfold fordNegativeUpperExplicit fordNegativeUpperBlock0
              fordNegativeUpperBlock1 fordNegativeUpperBlock2
            compute_degree
          omega
        have hprimitive : fordNegativePrimitiveExplicit.coeff (n + 1) = 0 := by
          apply Polynomial.coeff_eq_zero_of_natDegree_lt
          have hdegree : fordNegativePrimitiveExplicit.natDegree ≤ 55 := by
            unfold fordNegativePrimitiveExplicit fordNegativePrimitiveBlock0
              fordNegativePrimitiveBlock1 fordNegativePrimitiveBlock2
            compute_degree
          omega
        rw [hupper, hprimitive]
        simp

theorem fordBiDiagonal_fordNegativePrimitiveExplicit :
    fordBiDiagonal fordNegativePrimitiveExplicit =
      fordNegativeDiagonalExplicit := by
  apply Polynomial.funext
  intro y
  norm_num [fordBiDiagonal, fordNegativePrimitiveExplicit,
    fordNegativePrimitiveBlock0, fordNegativePrimitiveBlock1,
    fordNegativePrimitiveBlock2, fordNegativeDiagonalExplicit,
    fordNegativeDiagonalValueBlock0,
    fordNegativeDiagonalValueBlock1,
    fordNegativeDiagonalValueBlock2,
    fordNegativeDiagonalValueBlock3,
    fordNegativeDiagonalValueBlock4,
    fordNegativeUpperCoeff0,
    fordNegativeUpperCoeff1,
    fordNegativeUpperCoeff2,
    fordNegativeUpperCoeff3,
    fordNegativeUpperCoeff4,
    fordNegativeUpperCoeff5,
    fordNegativeUpperCoeff6,
    fordNegativeUpperCoeff7,
    fordNegativeUpperCoeff8,
    fordNegativeUpperCoeff9,
    fordNegativeUpperCoeff10,
    fordNegativeUpperCoeff11,
    fordNegativeUpperCoeff12,
    fordNegativeUpperCoeff13,
    fordNegativeUpperCoeff14,
    fordNegativeUpperCoeff15,
    fordNegativeUpperCoeff16,
    fordNegativeUpperCoeff17,
    fordNegativeUpperCoeff18,
    fordNegativeUpperCoeff19,
    fordNegativeUpperCoeff20,
    fordNegativeUpperCoeff21,
    fordNegativeUpperCoeff22,
    fordNegativeUpperCoeff23,
    fordNegativeUpperCoeff24,
    fordNegativeUpperCoeff25,
    fordNegativeUpperCoeff26,
    fordNegativeUpperCoeff27,
    fordNegativeUpperCoeff28,
    fordNegativeUpperCoeff29,
    fordNegativeUpperCoeff30,
    fordNegativeUpperCoeff31,
    fordNegativeUpperCoeff32,
    fordNegativeUpperCoeff33,
    fordNegativeUpperCoeff34,
    fordNegativeUpperCoeff35,
    fordNegativeUpperCoeff36,
    fordNegativeUpperCoeff37,
    fordNegativeUpperCoeff38,
    fordNegativeUpperCoeff39,
    fordNegativeUpperCoeff40,
    fordNegativeUpperCoeff41,
    fordNegativeUpperCoeff42,
    fordNegativeUpperCoeff43,
    fordNegativeUpperCoeff44,
    fordNegativeUpperCoeff45,
    fordNegativeUpperCoeff46,
    fordNegativeUpperCoeff47,
    fordNegativeUpperCoeff48,
    fordNegativeUpperCoeff49,
    fordNegativeUpperCoeff50,
    fordNegativeUpperCoeff51,
    fordNegativeUpperCoeff52,
    fordNegativeUpperCoeff53,
    fordNegativeUpperCoeff54]
  ring

theorem fordNegativeIntegralDiagonal_source_eq_explicit :
    fordBiDiagonal
        (fordBiIntegralPolynomial fordNegativeUpperPolynomial) =
      fordNegativeDiagonalExplicit := by
  rw [fordBiIntegralPolynomial_fordNegativeUpper_eq_explicit,
    fordBiDiagonal_fordNegativePrimitiveExplicit]

end

end GafniTao
