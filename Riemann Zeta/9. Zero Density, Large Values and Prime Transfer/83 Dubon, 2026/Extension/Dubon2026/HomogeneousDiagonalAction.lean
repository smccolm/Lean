import Dubon2026.HomogeneousDimension
import Dubon2026.GL2UnitDiagonalPair

/-! # Original diagonal matrix action on the genuine symmetric homogeneous model -/

namespace Dubon2026

noncomputable section

variable {R : Type*} [CommRing R]
open MvPolynomial Matrix

/-- A genuine diagonal matrix scales each original polynomial variable by its corresponding diagonal entry. -/
theorem matrixPolynomialAction_diagonal_X {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → R) (i : ι) :
    matrixPolynomialAction (Matrix.diagonal a) (X i) = a i • X i := by
  rw [matrixPolynomialAction_X]
  simp [Matrix.diagonal_apply]

/-- Actual diagonal substitution scales every genuine monomial by the product of its original coordinate weights. -/
theorem matrixPolynomialAction_diagonal_monomial {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → R) (d : ι →₀ ℕ) :
    matrixPolynomialAction (Matrix.diagonal a) (monomial d 1) =
      (d.prod (fun i m => a i ^ m)) • monomial d 1 := by
  rw [monomial_eq]
  simp only [map_one, one_mul, Finsupp.prod, map_prod, map_pow,
    matrixPolynomialAction_diagonal_X, smul_pow, Finset.prod_smul]

/-- An actual original degree-n monomial lies in the genuine homogeneous space. -/
def homogeneousMonomial {ι : Type*} (n : ℕ) (d : ι →₀ ℕ) (hd : d.degree = n) :
    homogeneousSubmodule ι R n :=
  ⟨monomial d 1, isHomogeneous_monomial 1 hd⟩

/-- The actual homogeneous diagonal action has the exact product weight on each original monomial. -/
theorem homogeneousMatrixAction_diagonal_monomial {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → R) (n : ℕ) (d : ι →₀ ℕ) (hd : d.degree = n) :
    homogeneousMatrixAction n (Matrix.diagonal a) (homogeneousMonomial n d hd) =
      (d.prod (fun i m => a i ^ m)) • homogeneousMonomial n d hd := by
  apply Subtype.ext
  exact matrixPolynomialAction_diagonal_monomial a d

end
end Dubon2026
