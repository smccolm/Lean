import Dubon2026.HomogeneousSymmetricMatrix

/-! # Exact coefficient change of the genuine symmetric-power general-linear matrices -/

namespace Dubon2026

noncomputable section
open MvPolynomial Matrix Module

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The original binary monomial basis maps to the same original binary monomial basis after changing its coefficients. -/
theorem binaryHomogeneousMonomialBasis_map (n : ℕ) (φ : R →+* S) (i : Fin (n + 1)) :
    homogeneousCoefficientMap n φ (binaryHomogeneousMonomialBasis n i) =
      binaryHomogeneousMonomialBasis n i := by
  simp only [binaryHomogeneousMonomialBasis, Basis.reindex_apply]
  rw [homogeneousMonomialBasis_apply (R := R), homogeneousMonomialBasis_apply (R := S)]
  apply Subtype.ext
  simp [homogeneousMonomial, homogeneousCoefficientMap]

/-- Every actual binary homogeneous coordinate undergoes exactly the original coefficient homomorphism. -/
theorem binaryHomogeneousMonomialBasis_repr_map (n : ℕ) (φ : R →+* S)
    (p : homogeneousSubmodule (Fin 2) R n) (i : Fin (n + 1)) :
    (binaryHomogeneousMonomialBasis n).repr (homogeneousCoefficientMap n φ p) i =
      φ ((binaryHomogeneousMonomialBasis n).repr p i) := by
  simp only [binaryHomogeneousMonomialBasis, Basis.repr_reindex_apply,
    homogeneousMonomialBasis_repr]
  exact MvPolynomial.coeff_map φ p.val _

/-- The genuine symmetric-power matrix homomorphism commutes with any homomorphism of the original commutative coefficient rings, including residue-field reduction. -/
theorem homogeneousSymmetricGL_map (n : ℕ) (φ : R →+* S)
    (g : GeneralLinearGroup (Fin 2) R) :
    GeneralLinearGroup.map φ (homogeneousSymmetricGL n g) =
      homogeneousSymmetricGL n (GeneralLinearGroup.map φ g) := by
  apply Units.ext
  ext i j
  change φ ((homogeneousSymmetricGL n g).val i j) =
    (homogeneousSymmetricGL n (GeneralLinearGroup.map φ g)).val i j
  rw [homogeneousSymmetricGL_val, homogeneousSymmetricGL_val,
    LinearMap.toMatrix_apply, LinearMap.toMatrix_apply,
    ← binaryHomogeneousMonomialBasis_repr_map n φ,
    homogeneousCoefficientMap_GL, binaryHomogeneousMonomialBasis_map]

end
end Dubon2026
