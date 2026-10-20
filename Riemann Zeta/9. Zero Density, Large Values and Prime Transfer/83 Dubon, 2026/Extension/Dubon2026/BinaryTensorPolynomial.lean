import Dubon2026.HomogeneousSymmetricMatrix
import Mathlib.Algebra.MvPolynomial.Equiv

/-! Two original binary polynomials in independent variables, with exact
coefficient extraction through Mathlib's iterated-polynomial equivalence.
This is the faithful coefficient bridge from the determinant covariant
to the original symmetric-power polarization matrix in DUB-17. -/

namespace Dubon2026
open MvPolynomial
noncomputable section

variable {R : Type*} [CommRing R]

/-- The original two binary polynomials placed in independent variable blocks. -/
def binaryTensorPolynomial (p q : MvPolynomial (Fin 2) R) : MvPolynomial (Fin 2 ⊕ Fin 2) R :=
  rename Sum.inl p * rename Sum.inr q

/-- Iterated-polynomial coordinates retain the two original factors exactly. -/
theorem binaryTensorPolynomial_iterated (p q : MvPolynomial (Fin 2) R) :
    sumAlgEquiv R (Fin 2) (Fin 2) (binaryTensorPolynomial p q) =
      MvPolynomial.map C p * C q := by
  have hl := AlgHom.congr_fun (sumAlgEquiv_comp_rename_inl R (Fin 2) (Fin 2)) p
  have hr := AlgHom.congr_fun (sumAlgEquiv_comp_rename_inr R (Fin 2) (Fin 2)) q
  change sumAlgEquiv R (Fin 2) (Fin 2) (rename Sum.inl p) = MvPolynomial.map C p at hl
  change sumAlgEquiv R (Fin 2) (Fin 2) (rename Sum.inr q) = C q at hr
  rw [binaryTensorPolynomial, map_mul, hl, hr]

/-- Extracting both actual coefficient blocks gives the product of the original coefficients. -/
theorem binaryTensorPolynomial_coeff (p q : MvPolynomial (Fin 2) R)
    (d e : Fin 2 →₀ ℕ) :
    coeff e (coeff d (sumAlgEquiv R (Fin 2) (Fin 2) (binaryTensorPolynomial p q))) =
      coeff d p * coeff e q := by
  rw [binaryTensorPolynomial_iterated, mul_comm, coeff_C_mul, coeff_map, mul_comm, coeff_C_mul]

end
end Dubon2026
