import Dubon2026.OriginalUnramifiedStageInUnion

/-! # Realize the scalar-stage fixed field in the same arithmetic union

The actual fixed field of the normalization subgroup is transported by
the original inclusion. Its values commute with the scalar-stage image,
so the prime-power class can be compared with the already proved class
invariants on literal intermediate fields of the arithmetic union.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ)

/-- Retain the actual rational structure of the arithmetic union. -/
local instance scalarFixedUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

/-- Retain the displayed rational structure of the scalar stage. -/
local instance scalarFixedFiniteAlgebra {V : Type} [Field V] [Algebra ℚ V]
    (F : FiniteGaloisIntermediateField ℚ V) : Algebra ℚ F := F.algebra'

/-- Retain the actual algebra on the fixed field and its intermediate-field image. -/
local instance scalarFixedIntermediateAlgebra {V : Type} [Field V] [Algebra ℚ V]
    (F : IntermediateField ℚ V) : Algebra ℚ F := F.algebra'

variable (L : OriginalUnramifiedGaloisStage (Ω := Ω) a) (S : Subgroup Gal(L.val/ℚ))

/-- The actual subgroup fixed field, embedded in the same arithmetic union. -/
def originalScalarFixedFieldInUnion : IntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (IntermediateField.fixedField S).map
    (IntermediateField.inclusion (originalUnramifiedGaloisStage_le_union a L))

/-- The fixed field's image equivalence preserves the original field element. -/
def originalScalarFixedFieldInUnionEquiv :
    IntermediateField.fixedField S ≃ₐ[ℚ] originalScalarFixedFieldInUnion Ω a L S :=
  IntermediateField.equivMap (IntermediateField.fixedField S)
    (IntermediateField.inclusion (originalUnramifiedGaloisStage_le_union a L))

/-- The fixed-field realization lies in the same realized scalar stage. -/
theorem originalScalarFixedFieldInUnion_le :
    originalScalarFixedFieldInUnion Ω a L S ≤ (originalUnramifiedStageInUnion a L).toIntermediateField := by
  rintro x ⟨y, _, rfl⟩
  exact ⟨y, rfl⟩

/-- Both original fixed-field inclusions give exactly the same upper-field
element, so their scalar towers are the actual commuting field towers. -/
theorem originalScalarFixedFieldInUnion_inclusion :
    (IntermediateField.inclusion (originalScalarFixedFieldInUnion_le Ω a L S)).comp
      (originalScalarFixedFieldInUnionEquiv Ω a L S).toAlgHom =
    (originalUnramifiedStageInUnionEquiv a L).toAlgHom.comp (IntermediateField.fixedField S).val := by
  ext x
  rfl

end
end Dubon2026
