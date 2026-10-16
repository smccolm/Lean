import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.SeparableClosure

/-! # Compositum Galois over the actual intermediate base

Change the scalar field of the literal intermediate fields and reuse
Mathlib's normal-compositum theorem. No rational normality is imposed on
the finite base or on its given Galois extension. This supplies the top
Galois condition in DUB-17's auxiliary class-generator tower.
-/
namespace Dubon2026
noncomputable section
open IntermediateField
attribute [-instance] SubfieldClass.instSMulRat

/-- The literal compositum of two Galois extensions of the same actual intermediate base is Galois over that base. -/
theorem originalRelativeGaloisCompositum_isGalois
    (U : Type) [Field U] [Algebra ℚ U]
    (K E L : IntermediateField ℚ U) (hKE : K ≤ E) (hKL : K ≤ L)
    (hGalKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      IsGalois K E)
    (hGalKL : letI : Algebra K L := (IntermediateField.inclusion hKL).toAlgebra
      IsGalois K L) :
    letI : Algebra K (E ⊔ L : IntermediateField ℚ U) :=
      (IntermediateField.inclusion (hKE.trans le_sup_left)).toAlgebra
    IsGalois K (E ⊔ L : IntermediateField ℚ U) := by
  let E' := IntermediateField.extendScalars hKE
  let L' := IntermediateField.extendScalars hKL
  letI : IsGalois K E' := hGalKE
  letI : IsGalois K L' := hGalKL
  have hsup : E' ⊔ L' = IntermediateField.extendScalars (hKE.trans le_sup_left : K ≤ E ⊔ L) := by
    apply IntermediateField.restrictScalars_injective ℚ
    rw [← IntermediateField.restrictScalars_sup,
      IntermediateField.extendScalars_restrictScalars,
      IntermediateField.extendScalars_restrictScalars,
      IntermediateField.extendScalars_restrictScalars]
  have hg : IsGalois K (E' ⊔ L' : IntermediateField K U) := ⟨⟩
  rw [hsup] at hg
  exact hg

end
end Dubon2026
