import Dubon2026.HomogeneousMonomialBasis
import Dubon2026.HomogeneousCoefficientChange
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # The genuine symmetric-power matrix homomorphism over arithmetic coefficient rings -/

namespace Dubon2026

noncomputable section
open MvPolynomial Matrix Module

variable {R : Type*} [CommRing R]

/-- The actual degree-n homogeneous action, expressed in its original binary monomial basis, is a homomorphism into the genuine rank-(n+1) general linear group. -/
def homogeneousSymmetricGL (n : ℕ) :
    GeneralLinearGroup (Fin 2) R →* GeneralLinearGroup (Fin (n + 1)) R :=
  (((LinearMap.toMatrixAlgEquiv (binaryHomogeneousMonomialBasis (R := R) n)).toAlgHom.toRingHom.toMonoidHom).comp
    (homogeneousGLRepresentation n)).toHomUnits

/-- The constructed symmetric-power general-linear matrix is the literal matrix of the original homogeneous action. -/
theorem homogeneousSymmetricGL_val (n : ℕ) (g : GeneralLinearGroup (Fin 2) R) :
    (homogeneousSymmetricGL n g).val =
      LinearMap.toMatrix (binaryHomogeneousMonomialBasis n) (binaryHomogeneousMonomialBasis n)
        (homogeneousGLRepresentation n g) := rfl

/-- Coordinates in the original fixed-degree monomial basis are exactly the original polynomial coefficients. -/
theorem homogeneousMonomialBasis_repr {ι : Type*} (n : ℕ)
    (p : homogeneousSubmodule ι R n) (d : {d : ι →₀ ℕ | d.degree = n}) :
    (homogeneousMonomialBasis n).repr p d = MvPolynomial.coeff d.val p.val := by
  classical
  let B := homogeneousMonomialBasis (R := R) (ι := ι) n
  have he : ((Finsupp.lapply d).comp B.repr.toLinearMap) =
      (MvPolynomial.lcoeff R d.val).comp (homogeneousSubmodule ι R n).subtype := by
    apply B.ext
    intro e
    change B.repr (B e) d = MvPolynomial.coeff d.val (B e).val
    rw [B.repr_self]
    rw [show B e = homogeneousMonomial (R := R) n e.val e.property from
      homogeneousMonomialBasis_apply n e]
    by_cases h : e = d
    · subst e
      simpa only [homogeneousMonomial, MvPolynomial.coeff_monomial, if_pos rfl] using
        (Finsupp.single_eq_same : (Finsupp.single d (1 : R)) d = 1)
    · have hv : e.val ≠ d.val := fun hv => h (Subtype.ext hv)
      simpa only [homogeneousMonomial, MvPolynomial.coeff_monomial, if_neg hv] using
        (Finsupp.single_eq_of_ne (Ne.symm h) : (Finsupp.single e (1 : R)) d = 0)
  exact congrArg (fun L : homogeneousSubmodule ι R n →ₗ[R] R => L p) he

/-- The binary monomial coordinate is the original polynomial coefficient at the literal exponent indexed by its first power. -/
theorem binaryHomogeneousMonomialBasis_repr (n : ℕ)
    (p : homogeneousSubmodule (Fin 2) R n) (i : Fin (n + 1)) :
    (binaryHomogeneousMonomialBasis n).repr p i =
      MvPolynomial.coeff (((binaryHomogeneousExponentEquiv n).trans Fin.revPerm).symm i).val p.val := by
  rw [binaryHomogeneousMonomialBasis, Basis.repr_reindex_apply, homogeneousMonomialBasis_repr]

end
end Dubon2026
