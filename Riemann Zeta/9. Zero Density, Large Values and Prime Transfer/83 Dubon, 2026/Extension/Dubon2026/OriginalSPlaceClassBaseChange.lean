import Dubon2026.OriginalSPlaceBaseChangeRepresentations

/-! # Actual transition maps on the source S-place idele classes

The proved original diagonal square descends the actual source idele map
to its literal quotient. The quotient map remains Galois equivariant.
This is the class transition, rather than an assumed transition certificate,
needed in the source fixed-support colimit for DUB-17's global-duality route.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K E L : Type) [Field K] [Field E] [NumberField E]
  [Field L] [NumberField L] [Algebra K E] [Algebra E L] [Algebra K L]
  [IsScalarTower K E L] [IsGalois K E]
  (S : Finset (HeightOneSpectrum (𝓞 E))) (T : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(E/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K E σ v ∈ S)
  (hT : ∀ (σ : Gal(L/K)) v, v ∈ T ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ T)
  (hST : ∀ w, w ∈ T ↔ originalFinitePrimeBelow E L w ∈ S)

/-- The literal source S-place idele map descends to the actual original class quotient. -/
def originalSPlaceClassBaseChangeRepHom :
    restrictedCoefficientRep (originalSPlaceIdeleClassRep K E S hS)
      (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K)) ⟶
      originalSPlaceIdeleClassRep K L T hT :=
  Rep.ofHom {
    toLinearMap := Submodule.mapQ
      (LinearMap.range (originalSPlacePrincipalRepHom K E S hS).hom.toLinearMap)
      (LinearMap.range (originalSPlacePrincipalRepHom K L T hT).hom.toLinearMap)
      (originalSPlaceBaseChangeRepHom K E L S T hS hT hST).hom.toLinearMap
      (by
        rintro _ ⟨x, rfl⟩
        exact ⟨(originalSUnitBaseChangeRepHom K E L S T hS hT hST).hom x,
          (originalSPlaceBaseChangeRepHom_principal K E L S T hS hT hST x).symm⟩)
    isIntertwining' := by
      intro σ
      apply LinearMap.ext
      intro x
      induction x using Submodule.Quotient.induction_on with
      | H y =>
        change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
        exact congrArg Submodule.Quotient.mk
          (Rep.hom_comm_apply (originalSPlaceBaseChangeRepHom K E L S T hS hT hST) σ y) }

/-- The class transition retains the original source idele representative under actual base change. -/
theorem originalSPlaceClassBaseChangeRepHom_mk
    (x : supportedUnrestrictedUnitRep K E S hS) :
    (originalSPlaceClassBaseChangeRepHom K E L S T hS hT hST).hom
      ((originalSPlaceIdeleClassRepHom K E S hS).hom x) =
        (originalSPlaceIdeleClassRepHom K L T hT).hom
          ((originalSPlaceBaseChangeRepHom K E L S T hS hT hST).hom x) := rfl

end
end Dubon2026
