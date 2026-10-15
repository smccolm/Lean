import Dubon2026.OriginalSPlaceBaseChange
import Dubon2026.OriginalIdeleGaloisTower
import Dubon2026.ContinuousRepresentationRestriction

/-! # Original Galois-equivariant transitions in the source idele sequence

The actual supported-idele base change intertwines normal restriction.
The existing equivariant local-factor maps then give the source S-place
transition and its original diagonal square, for the class-colimit route
needed by DUB-17 global duality.
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

/-- The actual supported-idele transition is equivariant for the original normal restriction. -/
def originalSupportedIdeleBaseChangeRepHom :
    restrictedCoefficientRep (originalSupportedIdeleRep K E S hS)
      (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K)) ⟶
      originalSupportedIdeleRep K L T hT :=
  Rep.ofHom {
    toLinearMap := (originalSupportedIdeleBaseChangeMap E L S T
      (fun w hw hv => hw ((hST w).mpr hv))).toAdditive.toIntLinearMap
    isIntertwining' := by
      intro σ
      apply LinearMap.ext
      intro x
      apply Additive.toMul.injective
      apply Subtype.ext
      exact (originalIdeleBaseChangeMap_restrictNormal K E L σ x.toMul.val).symm }

/-- The original source S-place map is equivariant for the same normal restriction. -/
def originalSPlaceBaseChangeRepHom :
    restrictedCoefficientRep (supportedUnrestrictedUnitRep K E S hS)
      (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K)) ⟶
      supportedUnrestrictedUnitRep K L T hT :=
  Rep.ofHom {
    toLinearMap := originalSPlaceBaseChange E L S T hST
    isIntertwining' := by
      intro σ
      apply LinearMap.ext
      intro x
      change (originalSupportedUnrestrictedProjection K L T hT).hom
        ((originalSupportedIdeleBaseChangeRepHom K E L S T hS hT hST).hom
          ((originalSPlaceSupportedInclusion K E S hS).hom
            ((supportedUnrestrictedUnitRep K E S hS).ρ (AlgEquiv.restrictNormalHom E σ) x))) = _
      rw [Rep.hom_comm_apply (originalSPlaceSupportedInclusion K E S hS)]
      change (originalSupportedUnrestrictedProjection K L T hT).hom
        ((originalSupportedIdeleBaseChangeRepHom K E L S T hS hT hST).hom
          ((restrictedCoefficientRep (originalSupportedIdeleRep K E S hS)
            (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K))).ρ σ
              ((originalSPlaceSupportedInclusion K E S hS).hom x))) = _
      rw [Rep.hom_comm_apply (originalSupportedIdeleBaseChangeRepHom K E L S T hS hT hST),
        Rep.hom_comm_apply (originalSupportedUnrestrictedProjection K L T hT)]
      rfl }

/-- The original field-unit embedding gives the actual equivariant S-unit transition. -/
def originalSUnitBaseChangeRepHom :
    restrictedCoefficientRep (sUnitOriginalRep K E S hS)
      (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K)) ⟶ sUnitOriginalRep K L T hT :=
  Rep.ofHom {
    toLinearMap := (originalValuationSUnitBaseChangeMap E L S T
      (fun w hw hv => hw ((hST w).mpr hv))).toAdditive.toIntLinearMap
    isIntertwining' := by
      intro σ
      apply LinearMap.ext
      intro x
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Units.ext
      exact AlgEquiv.restrictNormal_commutes σ E x.toMul.val.val }

/-- The actual equivariant S-unit and source idele transitions commute with the original diagonal inclusion. -/
theorem originalSPlaceBaseChangeRepHom_principal (x : sUnitOriginalRep K E S hS) :
    (originalSPlaceBaseChangeRepHom K E L S T hS hT hST).hom
      ((originalSPlacePrincipalRepHom K E S hS).hom x) =
        (originalSPlacePrincipalRepHom K L T hT).hom
          ((originalSUnitBaseChangeRepHom K E L S T hS hT hST).hom x) :=
  originalSPlaceBaseChange_principal E L S T hST x.toMul

end
end Dubon2026
