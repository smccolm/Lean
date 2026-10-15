import Dubon2026.OriginalOutsideUnitFixedDescent
import Dubon2026.OriginalClassQuotientInvariantLifting
import Dubon2026.OriginalClassesModOutsideBaseChange

/-! # Actual base-field classes modulo outside units are the invariants

The literal quotient inclusion is injective by outside-unit descent.
Outside-unit H1 vanishing and original full-class descent make its image
exactly the invariants. This is the finite invariant coefficient identity
needed for arithmetic class formation and DUB-17's global duality.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(K/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K K σ v ∈ S)
  (hT : ∀ (σ : Gal(L/K)) v, v ∈ T ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ T)
  (hST : ∀ w, w ∈ T ↔ originalFinitePrimeBelow K L w ∈ S)

/-- The actual full-class quotient inclusion is injective at the same pulled-back support. -/
theorem originalClassesModOutsideBaseChange_injective :
    Function.Injective (originalClassesModOutsideBaseChangeRepHom K K L S T hS hT hST).hom := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | H c =>
    change Submodule.Quotient.mk (Additive.ofMul
      (originalIdeleClassBaseChangeMap K L c.toMul)) = 0 at hx
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact originalFullClassBaseChange_reflects_outside K L S T hS hT hST c.toMul
      ((Submodule.Quotient.mk_eq_zero _).mp hx)

/-- Actual base classes modulo outside units map to the original quotient invariants. -/
def originalClassesModOutsideBaseInvariant :
    originalIdeleClassesModOutsideRep K K S hS →ₗ[ℤ]
      (originalIdeleClassesModOutsideRep K L T hT).ρ.invariants :=
  (originalClassesModOutsideBaseChangeRepHom K K L S T hS hT hST).hom.toLinearMap.codRestrict _
    (by
      intro x g
      induction x using Submodule.Quotient.induction_on with
      | H c =>
        change (originalIdeleClassesModOutsideRep K L T hT).ρ g
          ((originalIdeleClassesModOutsideRepHom K L T hT).hom
            (Additive.ofMul (originalIdeleClassBaseChangeMap K L c.toMul))) = _
        rw [← Rep.hom_comm_apply]
        exact congrArg (originalIdeleClassesModOutsideRepHom K L T hT).hom
          (congrArg Additive.ofMul (originalIdeleClassBaseChangeMap_fixed K L g c.toMul)))

/-- Every original invariant quotient class is the image of a unique actual base quotient class. -/
theorem originalClassesModOutsideBaseInvariant_bijective
    (hu : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ T → Algebra.IsUnramifiedAt ℤ w.asIdeal) :
    Function.Bijective (originalClassesModOutsideBaseInvariant K L S T hS hT hST) := by
  constructor
  · intro x y h
    exact originalClassesModOutsideBaseChange_injective K L S T hS hT hST
      (congrArg Subtype.val h)
  · intro x
    obtain ⟨c, hc⟩ := originalClassesModOutside_fixed_has_base_class K L T hT hu x.val x.property
    exact ⟨(originalIdeleClassesModOutsideRepHom K K S hS).hom (Additive.ofMul c), Subtype.ext hc⟩

/-- The original base class quotient and the literal upper class-quotient invariants are linearly equivalent. -/
def originalClassesModOutsideBaseInvariantEquiv
    (hu : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ T → Algebra.IsUnramifiedAt ℤ w.asIdeal) :
    originalIdeleClassesModOutsideRep K K S hS ≃ₗ[ℤ]
      (originalIdeleClassesModOutsideRep K L T hT).ρ.invariants :=
  LinearEquiv.ofBijective (originalClassesModOutsideBaseInvariant K L S T hS hT hST)
    (originalClassesModOutsideBaseInvariant_bijective K L S T hS hT hST hu)

end
end Dubon2026
