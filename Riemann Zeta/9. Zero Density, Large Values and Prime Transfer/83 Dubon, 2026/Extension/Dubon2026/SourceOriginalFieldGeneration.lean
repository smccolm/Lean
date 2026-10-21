import Dubon2026.SourceOriginalModularFunctionField

/-! DUB-17/18 -> original cusp-form lower dimension bound -> regular
differential realization -> injectivity of the actual differential expansion
-> separability over the actual j coordinate. The conditional consumer here uses
monic relations for divisor j series and derives finite extension.
SourceAllDivisorMonicRelations proves those relations and
SourceOriginalDifferentialInjectivity assembles the original-field result. Exact polynomial degree and irreducibility
are unnecessary for this finite-extension step.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_of_neZero.lean.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open IntermediateField Polynomial

theorem coeffEmb_algebraMap (L : Type*) [Field L] [Algebra ℚ L] (r : ℚ) :
    coeffEmb L (algebraMap ℚ (LaurentSeries ℚ) r) =
      algebraMap L (LaurentSeries L) (algebraMap ℚ L r) := by
  rw [SourceDifferential.algebraMap_laurentSeries_apply_alt, SourceDifferential.algebraMap_laurentSeries_apply_alt, coeffEmb,
    coeffMap_single]

theorem laurentBaseChange_full_eq_adjoin (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) :
    laurentBaseChange L (modularFunctionFieldFull N) =
      IntermediateField.adjoin L (⇑(coeffEmb L) '' divisorExpansions N) := by
  apply le_antisymm
  · rw [laurentBaseChange, adjoin_le_iff]
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ (modularFunctionFieldFull N).toSubfield := hx
    rw [modularFunctionFieldFull, adjoin_toSubfield] at hx'
    have hmem : coeffEmb L x ∈ (Subfield.closure
        (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ divisorExpansions N)).map (coeffEmb L) :=
      ⟨x, hx', rfl⟩
    rw [RingHom.map_field_closure] at hmem
    refine (Subfield.closure_le.2 ?_) hmem
    rintro _ ⟨y, hy, rfl⟩
    rcases hy with ⟨r, rfl⟩ | hy
    · rw [coeffEmb_algebraMap]
      exact (IntermediateField.adjoin L _).algebraMap_mem _
    · exact IntermediateField.subset_adjoin L _ ⟨y, hy, rfl⟩
  · rw [adjoin_le_iff]
    rintro _ ⟨y, hy, rfl⟩
    exact coeffEmb_mem_laurentBaseChange L (IntermediateField.subset_adjoin ℚ _ hy)


end
end Dubon2026.SourceFunctionField
