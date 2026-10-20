import Dubon2026.MatrixPolynomialAction
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic.Ring

/-! The actual binary determinant polynomial and its simultaneous matrix
covariance. Its nth power will provide the invariant coefficient matrix
for the existing homogeneous symmetric power, discharging the missing
conjugate-duality matrix in DUB-17's CM residual extension. -/

namespace Dubon2026
open MvPolynomial Matrix
noncomputable section

variable {R : Type*} [CommRing R]

/-- The original determinant of two binary vectors, in four independent variables. -/
def binaryDeterminantPolynomial : MvPolynomial (Fin 2 ⊕ Fin 2) R :=
  X (Sum.inl 0) * X (Sum.inr 1) - X (Sum.inl 1) * X (Sum.inr 0)

/-- Simultaneous original matrix substitution multiplies the binary determinant by the literal matrix determinant. -/
theorem binaryDeterminantPolynomial_covariance (g : Matrix (Fin 2) (Fin 2) R) :
    matrixPolynomialAction (Matrix.fromBlocks g 0 0 g) binaryDeterminantPolynomial =
      C g.det * binaryDeterminantPolynomial := by
  simp only [binaryDeterminantPolynomial, map_sub, map_mul, matrixPolynomialAction_X,
    Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.zero_apply, Matrix.det_fin_two, map_sub, map_mul, Algebra.smul_def]
  simp only [MvPolynomial.algebraMap_eq, map_zero, zero_mul, zero_add, add_zero]
  ring

/-- The determinant polynomial's original nth power has the exact symmetric-power multiplier. -/
theorem binaryDeterminantPolynomial_pow_covariance (g : Matrix (Fin 2) (Fin 2) R) (n : ℕ) :
    matrixPolynomialAction (Matrix.fromBlocks g 0 0 g) (binaryDeterminantPolynomial ^ n) =
      C (g.det ^ n) * binaryDeterminantPolynomial ^ n := by
  rw [map_pow, binaryDeterminantPolynomial_covariance, mul_pow, map_pow]

end
end Dubon2026
