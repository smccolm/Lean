import Dubon2026.OriginalIdeleClassInvariantNormQuotient
import Dubon2026.FiniteSecondCohomologySylowDetection

/-! # Degree bounds and exponent for the actual invariant class norm quotient

The existing original finite-H2 annihilation theorem gives the exact
exponent used in coprime cyclotomic base-change descent. Galois group
order equals extension degree under the actual Galois hypothesis.
The original base-field norm comparison remains a separate obligation
before this becomes the native global norm-index theorem in DUB-17.
-/

namespace Dubon2026
noncomputable section
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
attribute [local instance] IsCyclic.commGroup

/-- The actual invariant class norm quotient is finite and its order is at least the extension degree. -/
theorem originalIdeleClassInvariantNormQuotient_degree_lower
    (g : Gal(L/K)) (hg : ∀ σ, σ ∈ Subgroup.zpowers g) :
    Finite (OriginalIdeleClassInvariantNormQuotient K L g) ∧
      Module.finrank K L ≤ Nat.card (OriginalIdeleClassInvariantNormQuotient K L g) := by
  simpa only [IsGalois.card_aut_eq_finrank] using
    originalIdeleClassInvariantNormQuotient_order_lower K L g hg

/-- The extension degree annihilates the original invariant class norm quotient. -/
theorem originalIdeleClassInvariantNormQuotient_degree_nsmul_zero
    (g : Gal(L/K)) (hg : ∀ σ, σ ∈ Subgroup.zpowers g)
    (x : OriginalIdeleClassInvariantNormQuotient K L g) :
    Module.finrank K L • x = 0 := by
  let e := originalIdeleClassInvariantNormQuotientEquiv K L g hg
  apply e.injective
  change e.toAddEquiv.toAddMonoidHom (Module.finrank K L • x) = e.toAddEquiv.toAddMonoidHom 0
  rw [map_nsmul e.toAddEquiv.toAddMonoidHom, map_zero e.toAddEquiv.toAddMonoidHom]
  have h := finiteSecondCohomology_card_nsmul_eq_zero (originalIdeleClassRep K L) (e x)
  simpa only [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank] using h

end
end Dubon2026
