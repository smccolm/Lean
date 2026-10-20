import Dubon2026.BinaryTensorPolynomial

/-! Faithful four-variable encoding of matrices in the original binary
homogeneous basis. This connects the determinant covariant to the literal
symmetric-power matrices used in the DUB-17 residual representation. -/

namespace Dubon2026
open MvPolynomial Matrix Module
noncomputable section

variable {R : Type*} [CommRing R]

/-- The original binary monomial coefficient is exactly its basis Kronecker coefficient. -/
theorem binaryHomogeneousBasis_coeff (n : ℕ) (i j : Fin (n + 1)) :
    coeff (((binaryHomogeneousExponentEquiv n).trans Fin.revPerm).symm j).val
      (binaryHomogeneousMonomialBasis (R := R) n i).val = if i = j then 1 else 0 := by
  rw [← binaryHomogeneousMonomialBasis_repr, Basis.repr_self]
  simp [Finsupp.single_apply]

/-- Encode the literal original homogeneous matrix in two independent binary variable blocks. -/
def homogeneousMatrixPolynomial (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    MvPolynomial (Fin 2 ⊕ Fin 2) R :=
  ∑ i, ∑ j, A i j • binaryTensorPolynomial
    (binaryHomogeneousMonomialBasis n i).val (binaryHomogeneousMonomialBasis n j).val

/-- Two original coefficient extractions recover exactly the original matrix entry. -/
theorem homogeneousMatrixPolynomial_coeff (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (i j : Fin (n + 1)) :
    coeff (((binaryHomogeneousExponentEquiv n).trans Fin.revPerm).symm j).val
      (coeff (((binaryHomogeneousExponentEquiv n).trans Fin.revPerm).symm i).val
        (sumAlgEquiv R (Fin 2) (Fin 2) (homogeneousMatrixPolynomial n A))) = A i j := by
  simp only [homogeneousMatrixPolynomial, map_sum, map_smul, coeff_sum, coeff_smul,
    binaryTensorPolynomial_coeff, binaryHomogeneousBasis_coeff, smul_eq_mul]
  simp

/-- The four-variable encoding is faithful on the actual homogeneous coefficient matrices. -/
theorem homogeneousMatrixPolynomial_injective (n : ℕ) :
    Function.Injective (homogeneousMatrixPolynomial (R := R) n) := by
  intro A B h
  ext i j
  have he := congrArg (fun p : MvPolynomial (Fin 2 ⊕ Fin 2) R =>
    coeff (((binaryHomogeneousExponentEquiv n).trans Fin.revPerm).symm j).val
      (coeff (((binaryHomogeneousExponentEquiv n).trans Fin.revPerm).symm i).val
        (sumAlgEquiv R (Fin 2) (Fin 2) p))) h
  simpa only [homogeneousMatrixPolynomial_coeff] using he

end
end Dubon2026
