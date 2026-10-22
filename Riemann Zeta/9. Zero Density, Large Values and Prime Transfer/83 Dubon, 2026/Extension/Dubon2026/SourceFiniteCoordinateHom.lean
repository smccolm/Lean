import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Finiteness.Basic

/-! DUB-17/18 -> original Picard Hecke correspondence -> finite degeneracy
maps. A finite extension over the image of one coordinate is finite over
the entire source field. Native field-range equivalence and finite ring
homomorphism composition provide this transport. The original-field
consumer derives the finite-coordinate premise from its proved j theory.
-/
namespace Dubon2026.SourceCurve
noncomputable section
open IntermediateField

theorem finite_hom_of_finite_image_coordinate
    {K F E : Type*} [Field K] [Field F] [Field E] [Algebra K F] [Algebra K E]
    (φ : F →ₐ[K] E) (t : F)
    [FiniteDimensional (IntermediateField.adjoin K ({φ t} : Set E)) E] :
    φ.toRingHom.Finite := by
  let J := IntermediateField.adjoin K ({φ t} : Set E)
  letI : Algebra K J := J.toSubalgebra.algebra
  have hJ : J ≤ φ.fieldRange :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr ⟨t, rfl⟩)
  letI : Algebra J φ.fieldRange := (IntermediateField.inclusion hJ).toRingHom.toAlgebra
  letI : SMul J φ.fieldRange := (inferInstance : Algebra J φ.fieldRange).toSMul
  haveI : IsScalarTower J φ.fieldRange E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FiniteDimensional φ.fieldRange E :=
    Module.Finite.of_restrictScalars_finite J φ.fieldRange E
  have hv : φ.fieldRange.val.toRingHom.Finite := inferInstanceAs (Module.Finite φ.fieldRange E)
  let e := AlgEquiv.ofInjectiveField φ
  have he : φ.toRingHom = φ.fieldRange.val.toRingHom.comp e.toRingEquiv.toRingHom := by
    ext x
    rfl
  rw [he]
  exact hv.comp e.toRingEquiv.finite

end
end Dubon2026.SourceCurve
