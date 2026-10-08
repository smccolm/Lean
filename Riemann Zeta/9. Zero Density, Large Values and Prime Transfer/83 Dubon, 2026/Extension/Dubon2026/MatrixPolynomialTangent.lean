import Dubon2026.MatrixPolynomialDerivation
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.AlgebraMap

/-! # Exact original polynomial matrix tangent at the identity -/

namespace Dubon2026

noncomputable section
open MvPolynomial

variable {ι : Type*} [Fintype ι]

/-- The literal polynomial family obtained by substituting the columns of I+tA in the original generators. -/
def matrixPolynomialCurve (a : Matrix ι ι ℂ) :
    MvPolynomial ι ℂ →ₐ[ℂ] Polynomial (MvPolynomial ι ℂ) :=
  MvPolynomial.aeval (fun i => Polynomial.C (X i) +
    Polynomial.X * Polynomial.C (∑ j, a j i • X j))

/-- The actual matrix curve at the original variable is its literal affine column polynomial. -/
theorem matrixPolynomialCurve_X (a : Matrix ι ι ℂ) (i : ι) :
    matrixPolynomialCurve a (X i) = Polynomial.C (X i) +
      Polynomial.X * Polynomial.C (∑ j, a j i • X j) := MvPolynomial.aeval_X _ _

/-- The constant coefficient of the original matrix curve is the original polynomial itself. -/
theorem matrixPolynomialCurve_zero (a : Matrix ι ι ℂ) (p : MvPolynomial ι ℂ) :
    (matrixPolynomialCurve a p).coeff 0 = p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [matrixPolynomialCurve]
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]
  | mul_X p i hp => simp [map_mul, Polynomial.mul_coeff_zero, hp, matrixPolynomialCurve_X]

/-- The original first-order coefficient of matrix substitution equals the genuine original matrix derivation. -/
theorem matrixPolynomialCurve_one (a : Matrix ι ι ℂ) (p : MvPolynomial ι ℂ) :
    (matrixPolynomialCurve a p).coeff 1 = matrixPolynomialDerivation a p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [matrixPolynomialCurve]
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]
  | mul_X p i hp =>
      rw [map_mul, Polynomial.mul_coeff_one, matrixPolynomialCurve_zero, hp,
        Derivation.leibniz, matrixPolynomialDerivation_X]
      simp [matrixPolynomialCurve_X, smul_eq_mul, mul_comm]

/-- The formal derivative at zero of the original polynomial matrix orbit is the actual original matrix derivation. -/
theorem matrixPolynomialCurve_tangent (a : Matrix ι ι ℂ) (p : MvPolynomial ι ℂ) :
    Polynomial.eval 0 (Polynomial.derivative (matrixPolynomialCurve a p)) = matrixPolynomialDerivation a p := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
  simpa only [Nat.cast_zero, zero_add, mul_one] using matrixPolynomialCurve_one a p

end
end Dubon2026
