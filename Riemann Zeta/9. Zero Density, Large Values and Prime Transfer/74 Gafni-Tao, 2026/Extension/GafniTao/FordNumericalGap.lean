import GafniTao.FordExplicitPrimitives

/-!
# Source-derived polynomial gap in Ford's numerical integral estimate

This module separates the mathematical gap polynomial from its finite exact
certificate.  The definitions here are obtained from the analytic polynomial
majorants; the generated rational polynomial is connected in the subsequent
certificate module.
-/

namespace GafniTao

noncomputable section

def fordNumericalDenominator : Polynomial ℚ :=
  Polynomial.C (27 / 4) + Polynomial.C 9 * Polynomial.X

def fordNumericalCompactPolynomial : Polynomial ℚ :=
  fordBiDiagonal (fordBiIntegralPolynomial fordNegativeUpperPolynomial) +
    fordBiEvalV (fordBiIntegralPolynomial fordPositiveUpperPolynomial) (3 / 2)

def fordNumericalTailPolynomial : Polynomial ℚ :=
  fordBiEvalV fordTailUpperPolynomial 0

def fordNumericalNumerator : Polynomial ℚ :=
  fordNumericalDenominator * fordNumericalCompactPolynomial +
    fordNumericalTailPolynomial

def fordNumericalTarget : ℚ := 108754 / 100000

def fordNumericalGap : Polynomial ℚ :=
  Polynomial.C fordNumericalTarget * fordNumericalDenominator -
    fordNumericalNumerator

@[simp] theorem fordNumericalDenominator_eval (y : ℝ) :
    Polynomial.eval₂ (Rat.castHom ℝ) y fordNumericalDenominator =
      9 * y + 27 / 4 := by
  simp [fordNumericalDenominator]
  ring_nf

theorem fordNumericalCompactPolynomial_eval (y : ℝ) :
    Polynomial.eval₂ (Rat.castHom ℝ) y fordNumericalCompactPolynomial =
      fordBiPrimitiveValue fordNegativeUpperPolynomial y y +
        fordBiPrimitiveValue fordPositiveUpperPolynomial y (3 / 2) := by
  simp [fordNumericalCompactPolynomial, fordBiDiagonal_eval,
    fordBiEvalV_eval, fordBiIntegralPolynomial_eval]

theorem fordNumericalTailPolynomial_eval (y : ℝ) :
    Polynomial.eval₂ (Rat.castHom ℝ) y fordNumericalTailPolynomial =
      fordBiPolynomialEval fordTailUpperPolynomial y 0 := by
  simpa [fordNumericalTailPolynomial] using
    fordBiEvalV_eval fordTailUpperPolynomial 0 y

theorem fordNumericalNumerator_eval (y : ℝ) :
    Polynomial.eval₂ (Rat.castHom ℝ) y fordNumericalNumerator =
      (9 * y + 27 / 4) *
        (fordBiPrimitiveValue fordNegativeUpperPolynomial y y +
          fordBiPrimitiveValue fordPositiveUpperPolynomial y (3 / 2)) +
        fordBiPolynomialEval fordTailUpperPolynomial y 0 := by
  simp [fordNumericalNumerator, fordNumericalCompactPolynomial_eval,
    fordNumericalTailPolynomial_eval]

theorem fordNumericalPolynomialUpper_eq_ratio
    {y : ℝ} (hden : 9 * y + 27 / 4 ≠ 0) :
    fordNumericalPolynomialUpper y =
      Polynomial.eval₂ (Rat.castHom ℝ) y fordNumericalNumerator /
        Polynomial.eval₂ (Rat.castHom ℝ) y fordNumericalDenominator := by
  rw [fordNumericalNumerator_eval, fordNumericalDenominator_eval]
  unfold fordNumericalPolynomialUpper
  simp only [fordBiPrimitiveValue_zero, sub_zero]
  let A := fordBiPrimitiveValue fordNegativeUpperPolynomial y y
  let B := fordBiPrimitiveValue fordPositiveUpperPolynomial y (3 / 2)
  let C := fordBiPolynomialEval fordTailUpperPolynomial y 0
  let D := 9 * y + 27 / 4
  change A + B + C / D = (D * (A + B) + C) / D
  have hD : D ≠ 0 := by simpa [D] using hden
  field_simp [hD]

theorem fordNumericalGap_eval (y : ℝ) :
    Polynomial.eval₂ (Rat.castHom ℝ) y fordNumericalGap =
      (fordNumericalTarget : ℝ) * (9 * y + 27 / 4) -
        Polynomial.eval₂ (Rat.castHom ℝ) y fordNumericalNumerator := by
  simp [fordNumericalGap]

end

end GafniTao
