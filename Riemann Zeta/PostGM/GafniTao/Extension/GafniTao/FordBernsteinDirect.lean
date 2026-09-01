import GafniTao.FordNumericalIntegralUpper

/-!
# Direct exact Bernstein certificate for Ford's numerical integral

This module computes Bernstein coefficients from the source-defined Taylor
majorant.  Each numerical inequality is reduced to exact rational arithmetic
inside Lean; the external generator is not proof evidence.
-/

open Finset

namespace GafniTao

noncomputable section

set_option maxRecDepth 10000000

def fordDirectNumericalDenominator : Polynomial ℚ :=
  Polynomial.C (27 / 4) + Polynomial.C 9 * Polynomial.X

def fordDirectNegativePrimitiveDiagonal : Polynomial ℚ :=
  ∑ n ∈ Finset.range 55,
    (Polynomial.C (1 / (n + 1 : ℚ)) *
      fordNegativeUpperPolynomial.coeff n) * Polynomial.X ^ (n + 1)

def fordDirectPositivePrimitiveAtThreeHalves : Polynomial ℚ :=
  ∑ n ∈ Finset.range 199,
    (Polynomial.C (1 / (n + 1 : ℚ)) *
      fordPositiveUpperPolynomial.coeff n) *
        Polynomial.C ((3 / 2 : ℚ) ^ (n + 1))

def fordDirectNumericalCompact : Polynomial ℚ :=
  fordDirectNegativePrimitiveDiagonal +
    fordDirectPositivePrimitiveAtThreeHalves

def fordDirectNumericalTail : Polynomial ℚ :=
  fordTailUpperPolynomial.coeff 0

def fordDirectNumericalNumerator : Polynomial ℚ :=
  fordDirectNumericalDenominator * fordDirectNumericalCompact +
    fordDirectNumericalTail

def fordDirectNumericalGap : Polynomial ℚ :=
  Polynomial.C (108754 / 100000) * fordDirectNumericalDenominator -
    fordDirectNumericalNumerator

def fordDirectSubintervalMap (j : ℕ) : Polynomial ℚ :=
  Polynomial.C ((11 : ℚ) * (j : ℚ) / 80) +
    Polynomial.C (11 / 80 : ℚ) * Polynomial.X

def fordDirectAffineGap (j : ℕ) : Polynomial ℚ :=
  fordDirectNumericalGap.comp (fordDirectSubintervalMap j)

def fordDirectBernsteinCoefficient (j k : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (k + 1),
    (fordDirectAffineGap j).coeff i *
      (Nat.choose k i : ℚ) / (Nat.choose 88 i : ℚ)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem fordDirectBernsteinCoefficient_zero_zero :
    0 ≤ fordDirectBernsteinCoefficient 0 0 := by
  norm_num [fordDirectBernsteinCoefficient, fordDirectAffineGap,
    fordDirectSubintervalMap, fordDirectNumericalGap,
    fordDirectNumericalNumerator, fordDirectNumericalDenominator,
    fordDirectNumericalCompact, fordDirectNumericalTail,
    fordDirectNegativePrimitiveDiagonal,
    fordDirectPositivePrimitiveAtThreeHalves,
    fordNegativeUpperPolynomial, fordPositiveUpperPolynomial,
    fordTailUpperPolynomial, fordNegativePhasePolynomial,
    fordPositivePhasePolynomial, fordTailPhasePolynomial,
    fordScaledTaylorPolynomial, fordBiRat, fordBiY, fordBiV]
  simp [Polynomial.coeff_zero_eq_eval_zero]
  norm_num [Finset.sum_range_succ]

end

end GafniTao
