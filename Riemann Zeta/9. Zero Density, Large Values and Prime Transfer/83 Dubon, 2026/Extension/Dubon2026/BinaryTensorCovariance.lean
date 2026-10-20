import Dubon2026.BinaryTensorPolynomial
import Dubon2026.BinaryDeterminantCovariant

/-! Simultaneous substitution acts on each original binary factor. This
connects the four-variable determinant covariance to the already proved
homogeneous matrix action on the DUB-17 polarization route. -/

namespace Dubon2026
open MvPolynomial Matrix
noncomputable section

variable {R : Type*} [CommRing R]

/-- Simultaneous original matrix substitution commutes with the first binary variable inclusion. -/
theorem binaryDiagonalAction_rename_inl (g : Matrix (Fin 2) (Fin 2) R)
    (p : MvPolynomial (Fin 2) R) :
    matrixPolynomialAction (Matrix.fromBlocks g 0 0 g) (rename Sum.inl p) =
      rename Sum.inl (matrixPolynomialAction g p) := by
  have he : (matrixPolynomialAction (Matrix.fromBlocks g 0 0 g)).comp (rename Sum.inl) =
      (rename Sum.inl).comp (matrixPolynomialAction g) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [matrixPolynomialAction_X, Fintype.sum_sum_type]
  exact AlgHom.congr_fun he p

/-- Simultaneous original matrix substitution commutes with the second binary variable inclusion. -/
theorem binaryDiagonalAction_rename_inr (g : Matrix (Fin 2) (Fin 2) R)
    (p : MvPolynomial (Fin 2) R) :
    matrixPolynomialAction (Matrix.fromBlocks g 0 0 g) (rename Sum.inr p) =
      rename Sum.inr (matrixPolynomialAction g p) := by
  have he : (matrixPolynomialAction (Matrix.fromBlocks g 0 0 g)).comp (rename Sum.inr) =
      (rename Sum.inr).comp (matrixPolynomialAction g) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [matrixPolynomialAction_X, Fintype.sum_sum_type]
  exact AlgHom.congr_fun he p

/-- The actual simultaneous action on a two-factor polynomial is the original action on both factors. -/
theorem binaryTensorPolynomial_covariance (g : Matrix (Fin 2) (Fin 2) R)
    (p q : MvPolynomial (Fin 2) R) :
    matrixPolynomialAction (Matrix.fromBlocks g 0 0 g) (binaryTensorPolynomial p q) =
      binaryTensorPolynomial (matrixPolynomialAction g p) (matrixPolynomialAction g q) := by
  rw [binaryTensorPolynomial, map_mul, binaryDiagonalAction_rename_inl, binaryDiagonalAction_rename_inr]
  rfl

/-- Original finite linear combinations in both homogeneous factors expand with the product coefficients. -/
theorem binaryTensorPolynomial_sum_smul (n : ℕ) (a b : Fin (n + 1) → R)
    (p q : Fin (n + 1) → MvPolynomial (Fin 2) R) :
    binaryTensorPolynomial (∑ i, a i • p i) (∑ j, b j • q j) =
      ∑ i, ∑ j, (a i * b j) • binaryTensorPolynomial (p i) (q j) := by
  simp only [binaryTensorPolynomial, map_sum, map_smul, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

end
end Dubon2026
