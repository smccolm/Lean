import Dubon2026.OriginalOutsideClassBaseChange

/-! # Fixed-support full-class quotient transitions

The literal full idele-class map descends modulo actual outside units.
The original source S-place comparison commutes with that transition.
This supplies the natural comparison system for DUB-17, without asserting
the principalization needed for surjectivity in the arithmetic colimit.
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

/-- The actual full-class transition modulo the original outside-unit images. -/
def originalClassesModOutsideBaseChangeRepHom :
    restrictedCoefficientRep (originalIdeleClassesModOutsideRep K E S hS)
      (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K)) ⟶
      originalIdeleClassesModOutsideRep K L T hT :=
  Rep.ofHom {
    toLinearMap := Submodule.mapQ
      (LinearMap.range (originalOutsideIdeleClassRepHom K E S hS).hom.toLinearMap)
      (LinearMap.range (originalOutsideIdeleClassRepHom K L T hT).hom.toLinearMap)
      (originalFullClassBaseChangeRepHom K E L).hom.toLinearMap
      (originalFullClassBaseChange_preserves_outside K E L S T hS hT hST)
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro x
      induction x using Submodule.Quotient.induction_on with
      | H y =>
        change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
        exact congrArg Submodule.Quotient.mk
          (Rep.hom_comm_apply (originalFullClassBaseChangeRepHom K E L) g y) }

/-- The quotient transition retains the literal original full-class representative. -/
theorem originalClassesModOutsideBaseChangeRepHom_mk (x : originalIdeleClassRep K E) :
    (originalClassesModOutsideBaseChangeRepHom K E L S T hS hT hST).hom
      ((originalIdeleClassesModOutsideRepHom K E S hS).hom x) =
        (originalIdeleClassesModOutsideRepHom K L T hT).hom
          ((originalFullClassBaseChangeRepHom K E L).hom x) := rfl

private theorem supported_class_eq_of_projection
    (x y : originalSupportedIdeleRep K L T hT)
    (h : (supportedIdeleLocalFactorLinearEquiv L T x).1 =
      (supportedIdeleLocalFactorLinearEquiv L T y).1) :
    (originalIdeleClassesModOutsideRepHom K L T hT).hom
      ((originalSupportedClassRepHom K L T hT).hom x) =
        (originalIdeleClassesModOutsideRepHom K L T hT).hom
          ((originalSupportedClassRepHom K L T hT).hom y) := by
  apply sub_eq_zero.mp
  rw [← map_sub, ← map_sub]
  change Submodule.Quotient.mk ((originalSupportedClassRepHom K L T hT).hom (x - y)) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  let e := supportedIdeleLocalFactorLinearEquiv L T
  refine ⟨(e (x - y)).2, ?_⟩
  change (originalSupportedClassRepHom K L T hT).hom
    ((originalOutsideSupportedInclusion K L T hT).hom (e (x - y)).2) = _
  congr 1
  apply e.injective
  change e (e.symm (0, (e (x - y)).2)) = e (x - y)
  rw [e.apply_symm_apply]
  apply Prod.ext
  · change 0 = (e (x - y)).1
    exact ((congrArg Prod.fst (e.map_sub x y)).trans (sub_eq_zero.mpr h)).symm
  · rfl

/-- Every original supported idele has its full-class quotient image represented by its actual S-place projection. -/
theorem originalSPlaceClassComparison_of_supported
    (x : originalSupportedIdeleRep K L T hT) :
    (originalSPlaceClassComparison K L T hT).hom
      ((originalSPlaceIdeleClassRepHom K L T hT).hom
        ((originalSupportedUnrestrictedProjection K L T hT).hom x)) =
      (originalIdeleClassesModOutsideRepHom K L T hT).hom
        ((originalSupportedClassRepHom K L T hT).hom x) := by
  apply supported_class_eq_of_projection
  have he := (supportedIdeleLocalFactorLinearEquiv L T).apply_symm_apply
    ((supportedIdeleLocalFactorLinearEquiv L T x).1, 0)
  have hp := congrArg Prod.fst he
  exact hp

/-- The original source-class comparison commutes with full-class base change modulo outside units. -/
theorem originalSPlaceClassComparison_baseChange
    (x : originalSPlaceIdeleClassRep K E S hS) :
    (originalClassesModOutsideBaseChangeRepHom K E L S T hS hT hST).hom
      ((originalSPlaceClassComparison K E S hS).hom x) =
        (originalSPlaceClassComparison K L T hT).hom
          ((originalSPlaceClassBaseChangeRepHom K E L S T hS hT hST).hom x) := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    change (originalIdeleClassesModOutsideRepHom K L T hT).hom
      ((originalFullClassBaseChangeRepHom K E L).hom
        ((originalSupportedClassRepHom K E S hS).hom
          ((originalSPlaceSupportedInclusion K E S hS).hom x))) = _
    rw [originalFullClassBaseChange_supported K E L S T hS hT hST]
    apply supported_class_eq_of_projection
    have hp := originalSPlaceBaseChange_projection E L S T hST
      ((originalSPlaceSupportedInclusion K E S hS).hom x)
    have hx : (supportedIdeleLocalFactorLinearEquiv E S
        ((originalSPlaceSupportedInclusion K E S hS).hom x)).1 = x :=
      congrArg Prod.fst ((supportedIdeleLocalFactorLinearEquiv E S).apply_symm_apply (x, 0))
    rw [hx] at hp
    exact hp.symm.trans (congrArg Prod.fst
      ((supportedIdeleLocalFactorLinearEquiv L T).apply_symm_apply
        ((originalSPlaceBaseChangeRepHom K E L S T hS hT hST).hom x, 0))).symm

end
end Dubon2026
