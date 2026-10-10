import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! # The literal field ranges of the two original compositum inclusions -/

namespace Dubon2026

noncomputable section

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

/-- The two original inclusions into the actual supremum generate that entire original compositum as a field. -/
theorem intermediateField_sup_inclusion_ranges (E F : IntermediateField K Ω) :
    (IntermediateField.inclusion (show E ≤ E ⊔ F from le_sup_left)).toRingHom.fieldRange ⊔
      (IntermediateField.inclusion (show F ≤ E ⊔ F from le_sup_right)).toRingHom.fieldRange =
        ⊤ := by
  let S := E ⊔ F
  let i := IntermediateField.inclusion (show E ≤ S from le_sup_left)
  let j := IntermediateField.inclusion (show F ≤ S from le_sup_right)
  have hi : i.toRingHom.fieldRange.map S.val.toRingHom = E.toSubfield := by
    rw [RingHom.map_fieldRange]
    change E.val.fieldRange.toSubfield = E.toSubfield
    rw [IntermediateField.fieldRange_val]
  have hj : j.toRingHom.fieldRange.map S.val.toRingHom = F.toSubfield := by
    rw [RingHom.map_fieldRange]
    change F.val.fieldRange.toSubfield = F.toSubfield
    rw [IntermediateField.fieldRange_val]
  have htop : (⊤ : Subfield S).map S.val.toRingHom = S.toSubfield := by
    rw [← RingHom.fieldRange_eq_map]
    change S.val.fieldRange.toSubfield = S.toSubfield
    rw [IntermediateField.fieldRange_val]
  have hmap : (i.toRingHom.fieldRange ⊔ j.toRingHom.fieldRange).map S.val.toRingHom =
      (⊤ : Subfield S).map S.val.toRingHom := by
    rw [Subfield.map_sup, hi, hj, htop]
    exact (IntermediateField.sup_toSubfield E F).symm
  have h := congrArg (Subfield.comap S.val.toRingHom) hmap
  simpa only [Subfield.comap_map] using h

end
end Dubon2026
