import Dubon2026.OriginalSPlaceClassBaseChange

/-! # Original outside-unit class images under base change

The source projection square proves that the original full-class transition
preserves the outside-unit image. This is the necessary quotient transition
for the fixed-support class comparison in DUB-17 global duality. It assumes
neither capitulation nor surjectivity of the source class comparison.
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

/-- The literal full idele-class transition as a morphism for normal restriction. -/
def originalFullClassBaseChangeRepHom :
    restrictedCoefficientRep (originalIdeleClassRep K E)
      (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K)) ⟶
      originalIdeleClassRep K L :=
  Rep.ofHom {
    toLinearMap := (originalIdeleClassBaseChangeMap E L).toAdditive.toIntLinearMap
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro x
      exact congrArg Additive.ofMul
        (originalIdeleClassBaseChangeMap_restrictNormal K E L g x.toMul).symm }

/-- The original full-class transition commutes with the actual supported-idele class map. -/
theorem originalFullClassBaseChange_supported
    (x : originalSupportedIdeleRep K E S hS) :
    (originalFullClassBaseChangeRepHom K E L).hom
      ((originalSupportedClassRepHom K E S hS).hom x) =
        (originalSupportedClassRepHom K L T hT).hom
          ((originalSupportedIdeleBaseChangeRepHom K E L S T hS hT hST).hom x) := by
  exact congrArg Additive.ofMul (originalIdeleClassBaseChangeMap_mk E L x.toMul.val)

/-- Base change of an original outside-unit idele remains an original outside-unit idele. -/
theorem originalSupportedBaseChange_outside
    (x : supportedOutsideUnitRep K E S hS) :
    ∃ y : supportedOutsideUnitRep K L T hT,
      (originalOutsideSupportedInclusion K L T hT).hom y =
        (originalSupportedIdeleBaseChangeRepHom K E L S T hS hT hST).hom
          ((originalOutsideSupportedInclusion K E S hS).hom x) := by
  let z := (originalSupportedIdeleBaseChangeRepHom K E L S T hS hT hST).hom
    ((originalOutsideSupportedInclusion K E S hS).hom x)
  let e := supportedIdeleLocalFactorLinearEquiv L T
  refine ⟨(e z).2, ?_⟩
  apply e.injective
  change e (e.symm (0, (e z).2)) = e z
  rw [e.apply_symm_apply]
  apply Prod.ext
  · have hp := originalSPlaceBaseChange_projection E L S T hST
      ((originalOutsideSupportedInclusion K E S hS).hom x)
    have hx : (supportedIdeleLocalFactorLinearEquiv E S
        ((originalOutsideSupportedInclusion K E S hS).hom x)).1 = 0 :=
      congrArg Prod.fst ((supportedIdeleLocalFactorLinearEquiv E S).apply_symm_apply (0, x))
    rw [hx, map_zero] at hp
    exact hp
  · rfl

include hST in
/-- The literal full-class transition preserves the original outside-unit class image. -/
theorem originalFullClassBaseChange_preserves_outside :
    LinearMap.range (originalOutsideIdeleClassRepHom K E S hS).hom.toLinearMap ≤
      (LinearMap.range (originalOutsideIdeleClassRepHom K L T hT).hom.toLinearMap).comap
        (originalFullClassBaseChangeRepHom K E L).hom.toLinearMap := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := originalSupportedBaseChange_outside K E L S T hS hT hST x
  refine ⟨y, ?_⟩
  change (originalSupportedClassRepHom K L T hT).hom
    ((originalOutsideSupportedInclusion K L T hT).hom y) = _
  rw [hy]
  exact (originalFullClassBaseChange_supported K E L S T hS hT hST _).symm

end
end Dubon2026
