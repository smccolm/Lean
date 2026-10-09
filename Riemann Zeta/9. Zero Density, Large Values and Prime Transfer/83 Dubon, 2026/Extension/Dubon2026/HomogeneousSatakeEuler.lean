import Dubon2026.HomogeneousMonomialBasis
import Dubon2026.SymmetricEulerPolynomial
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # The genuine homogeneous representation gives the original symmetric Euler polynomial -/

namespace Dubon2026

noncomputable section
open MvPolynomial Matrix Module

/-- In the actual binary monomial basis, diagonal substitution has the original degree-n symmetric weights. -/
theorem binaryHomogeneousMonomialBasis_diagonal (a b : ℂ) (n : ℕ) (i : Fin (n + 1)) :
    homogeneousMatrixAction n (Matrix.diagonal ![a, b]) (binaryHomogeneousMonomialBasis n i) =
      (a ^ i.val * b ^ (n - i.val)) • binaryHomogeneousMonomialBasis n i := by
  unfold binaryHomogeneousMonomialBasis
  rw [Basis.reindex_apply, homogeneousMonomialBasis_apply, homogeneousMatrixAction_diagonal_monomial]
  congr 1
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
  change a ^ (n - i.rev.val) * b ^ i.rev.val = _
  have hr : i.rev.val = n - i.val := by simp [Fin.val_rev]
  rw [hr, Nat.sub_sub_self (Nat.le_of_lt_succ i.isLt)]

/-- The actual matrix of original diagonal substitution is precisely diagonal with the genuine symmetric-power eigenvalues. -/
theorem homogeneousDiagonal_toMatrix (a b : ℂ) (n : ℕ) :
    LinearMap.toMatrix (binaryHomogeneousMonomialBasis n) (binaryHomogeneousMonomialBasis n)
      (homogeneousMatrixAction n (Matrix.diagonal ![a, b])) =
        Matrix.diagonal (fun i : Fin (n + 1) => a ^ i.val * b ^ (n - i.val)) := by
  ext i j
  rw [LinearMap.toMatrix_apply, binaryHomogeneousMonomialBasis_diagonal]
  by_cases h : i = j
  · subst j
    simp
  · simp [h]

/-- The literal determinant Euler polynomial of the actual original homogeneous matrix action. -/
def homogeneousMatrixEulerPolynomial (n : ℕ) (g : Matrix (Fin 2) (Fin 2) ℂ) : Polynomial ℂ :=
  Matrix.det ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) (Polynomial ℂ)) - (Polynomial.X : Polynomial ℂ) •
    (LinearMap.toMatrix (binaryHomogeneousMonomialBasis n) (binaryHomogeneousMonomialBasis n)
      (homogeneousMatrixAction n g)).map Polynomial.C)

/-- The determinant of the genuine symmetric homogeneous diagonal action equals the original finite spectral Euler polynomial. -/
theorem homogeneousDiagonal_euler (a b : ℂ) (n : ℕ) :
    homogeneousMatrixEulerPolynomial n (Matrix.diagonal ![a, b]) = symmetricEulerPolynomial a b n := by
  rw [homogeneousMatrixEulerPolynomial, homogeneousDiagonal_toMatrix]
  have he : (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) (Polynomial ℂ)) - (Polynomial.X : Polynomial ℂ) •
      (Matrix.diagonal (fun i : Fin (n + 1) => a ^ i.val * b ^ (n - i.val))).map Polynomial.C =
      Matrix.diagonal (fun i : Fin (n + 1) => 1 - Polynomial.C (a ^ i.val * b ^ (n - i.val)) * Polynomial.X) := by
    ext i j
    by_cases h : i = j
    · subst j
      simp [mul_comm]
    · simp [h]
  rw [he, Matrix.det_diagonal]
  exact Fin.prod_univ_eq_prod_range (fun i => 1 - Polynomial.C (a ^ i * b ^ (n - i)) * Polynomial.X) (n + 1)

/-- The genuine general-linear diagonal of the two original units has exactly its symmetric Euler polynomial in the actual homogeneous representation. -/
theorem homogeneousUnitDiagonal_euler (a b : ℂˣ) (n : ℕ) :
    homogeneousMatrixEulerPolynomial n (gl2UnitDiagonalPair a b).val =
      symmetricEulerPolynomial a.val b.val n := by
  have he : (gl2UnitDiagonalPair a b).val = Matrix.diagonal ![a.val, b.val] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [he, homogeneousDiagonal_euler]

end
end Dubon2026
