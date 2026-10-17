import Dubon2026.OriginalInvariantNormQuotientEquiv
import Dubon2026.OriginalIdeleClassNativeNormQuotient

/-! # The literal full idele-class norm quotient for a finite Galois extension

Existing original fixed-class descent identifies the full invariant
coefficient with base classes without a cyclicity assumption. The
actual product formula identifies both norm ranges. This is the
arithmetic model comparison needed by DUB-17's abelian norm-field route.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module
  Submodule.Quotient.module

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- Actual base classes map to all original full-class invariants. -/
def originalFullClassBaseInvariant :
    Additive (OriginalNumberFieldIdeleClassGroup K) →ₗ[ℤ]
      (originalIdeleClassRep K L).ρ.invariants :=
  (originalIdeleClassBaseChangeMap K L).toAdditive.toIntLinearMap.codRestrict
    (originalIdeleClassRep K L).ρ.invariants (fun c g =>
      congrArg Additive.ofMul (originalIdeleClassBaseChangeMap_fixed K L g c.toMul))

/-- Existing original fixed-class descent identifies the base classes with every full-class invariant. -/
def originalFullClassBaseInvariantEquiv :
    Additive (OriginalNumberFieldIdeleClassGroup K) ≃ₗ[ℤ]
      (originalIdeleClassRep K L).ρ.invariants :=
  LinearEquiv.ofBijective (originalFullClassBaseInvariant K L) (by
    constructor
    · intro c d h
      apply Additive.toMul.injective
      apply originalIdeleClassBaseChangeMap_injective K L
      exact congrArg (fun z => Additive.toMul z.val) h
    · intro x
      obtain ⟨c, hc⟩ := originalIdeleClassBaseChangeMap_surjective_fixed K L x.val.toMul
        (fun g => congrArg Additive.toMul (x.property g))
      exact ⟨Additive.ofMul c, Subtype.ext (congrArg Additive.ofMul hc)⟩)

/-- The actual descended field norm becomes the literal invariant norm under original base-class descent. -/
theorem originalFullClassBaseInvariant_norm
    (c : Additive (OriginalNumberFieldIdeleClassGroup L)) :
    originalFullClassBaseInvariantEquiv K L (originalIdeleClassNormLinear K L c) =
      originalInvariantNormLinear (originalIdeleClassRep K L) c := by
  apply Subtype.ext
  apply Additive.toMul.injective
  exact (originalIdeleClassBaseChangeMap_norm K L c.toMul).trans
    (originalIdeleClass_representation_norm K L c.toMul).symm

/-- Actual full-class descent identifies exactly the descended norm image with the original invariant norm range. -/
theorem originalFullClassBaseInvariant_norm_range :
    (originalIdeleClassNormLinear K L).range.map
      (originalFullClassBaseInvariantEquiv K L).toLinearMap =
        (originalInvariantNormLinear (originalIdeleClassRep K L)).range := by
  ext x
  constructor
  · rintro ⟨c, ⟨b, rfl⟩, rfl⟩
    exact ⟨b, (originalFullClassBaseInvariant_norm K L b).symm⟩
  · rintro ⟨b, rfl⟩
    exact ⟨originalIdeleClassNormLinear K L b, ⟨b, rfl⟩,
      originalFullClassBaseInvariant_norm K L b⟩

/-- The existing literal field class-norm quotient is the actual invariant norm quotient for every finite Galois extension. -/
def originalFullClassNormQuotientEquiv :
    OriginalIdeleClassNormQuotient K L ≃ₗ[ℤ]
      OriginalInvariantNormQuotient (originalIdeleClassRep K L) :=
  Submodule.Quotient.equiv _ _ (originalFullClassBaseInvariantEquiv K L)
    (originalFullClassBaseInvariant_norm_range K L)

end
end Dubon2026
