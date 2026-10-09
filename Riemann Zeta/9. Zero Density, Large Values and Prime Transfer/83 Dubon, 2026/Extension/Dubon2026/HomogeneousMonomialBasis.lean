import Dubon2026.HomogeneousDiagonalAction
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Data.Fin.Rev

/-! # The genuine monomial basis of the original homogeneous representation -/

namespace Dubon2026

noncomputable section

variable {R : Type*} [CommRing R]
open MvPolynomial Module

/-- The original fixed-degree monomials are linearly independent in their actual homogeneous space. -/
theorem homogeneousMonomial_linearIndependent {ι : Type*} (n : ℕ) :
    LinearIndependent R (fun d : {d : ι →₀ ℕ | d.degree = n} =>
      homogeneousMonomial (R := R) n d.val d.property) := by
  apply LinearIndependent.of_comp (homogeneousSubmodule ι R n).subtype
  exact (basisMonomials ι R).linearIndependent.comp Subtype.val Subtype.val_injective

/-- The original degree-n monomials span the entire genuine homogeneous polynomial space. -/
theorem homogeneousMonomial_span {ι : Type*} (n : ℕ) :
    Submodule.span R (Set.range (fun d : {d : ι →₀ ℕ | d.degree = n} =>
      homogeneousMonomial (R := R) n d.val d.property)) = ⊤ := by
  apply (Submodule.span_range_subtype_eq_top_iff (homogeneousSubmodule ι R n) _).mpr
  rw [homogeneousSubmodule_eq_finsupp_supported, Finsupp.supported_eq_span_single]
  congr 1
  ext p
  constructor
  · rintro ⟨d, rfl⟩
    exact ⟨d.val, d.property, rfl⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨⟨d, hd⟩, rfl⟩

/-- The original monomials give a genuine basis of the full homogeneous polynomial space. -/
def homogeneousMonomialBasis {ι : Type*} (n : ℕ) :
    Basis {d : ι →₀ ℕ | d.degree = n} R (homogeneousSubmodule ι R n) :=
  Basis.mk (homogeneousMonomial_linearIndependent n) (homogeneousMonomial_span n).ge

/-- Every vector in the actual monomial basis is its literal original homogeneous monomial. -/
theorem homogeneousMonomialBasis_apply {ι : Type*} (n : ℕ)
    (d : {d : ι →₀ ℕ | d.degree = n}) :
    homogeneousMonomialBasis (R := R) n d = homogeneousMonomial n d.val d.property :=
  Basis.mk_apply _ _ d

/-- The original binary monomial basis is indexed by the first exponent i from zero through n. -/
def binaryHomogeneousMonomialBasis (n : ℕ) :
    Basis (Fin (n + 1)) R (homogeneousSubmodule (Fin 2) R n) :=
  (homogeneousMonomialBasis n).reindex ((binaryHomogeneousExponentEquiv n).trans Fin.revPerm)

end
end Dubon2026
