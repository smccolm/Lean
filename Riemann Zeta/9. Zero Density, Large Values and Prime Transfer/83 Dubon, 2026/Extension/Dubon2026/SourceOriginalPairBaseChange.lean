import Dubon2026.SourceOriginalAllLevelDegree

/-! DUB-17/18 -> numerical modular genus -> cusp classification -> actual
Laurent embeddings after coefficient extension. The proved rational pair
generation transports through the existing literal coefficient extension.
Both generators are actual elements of the original field, and they
generate that field internally. This is the input to the minimal-polynomial
embedding construction used to classify the places over infinity.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open IntermediateField
open scoped IntermediateField
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L]

/-- The actual level-N j series inside the original coefficient-extended field. -/
def jNOver : modularFunctionFieldOver N L :=
  ⟨coeffEmb L (qExpand ℚ N jq), coeffEmb_mem_laurentBaseChange L (jqd_mem_full N dvd_rfl)⟩

theorem original_field_eq_pair_over :
    modularFunctionFieldOver N L = IntermediateField.adjoin L
      ({coeffEmb L jq, coeffEmb L (qExpand ℚ N jq)} : Set (LaurentSeries L)) := by
  rw [modularFunctionFieldOver, original_full_eq_pair, laurentBaseChange]
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, hx, rfl⟩
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · exact subset_adjoin L _ (Set.mem_insert _ _)
      · rcases hx with rfl
        exact subset_adjoin L _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    | algebraMap r =>
      rw [coeffEmb_algebraMap]
      exact IntermediateField.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  · rw [IntermediateField.adjoin_le_iff]
    rintro x (rfl | hx)
    · exact subset_adjoin L _ ⟨jq, subset_adjoin ℚ _ (Set.mem_insert _ _), rfl⟩
    · rcases hx with rfl
      exact subset_adjoin L _ ⟨qExpand ℚ N jq,
        subset_adjoin ℚ _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)), rfl⟩

theorem original_field_eq_simple_restrict_over :
    modularFunctionFieldOver N L =
      (IntermediateField.adjoin (IntermediateField.adjoin L
        ({coeffEmb L jq} : Set (LaurentSeries L)))
        ({coeffEmb L (qExpand ℚ N jq)} : Set (LaurentSeries L))).restrictScalars L := by
  rw [original_field_eq_pair_over]
  simpa only [Set.singleton_union] using
    (adjoin_adjoin_left L ({coeffEmb L jq} : Set (LaurentSeries L))
      ({coeffEmb L (qExpand ℚ N jq)} : Set (LaurentSeries L))).symm

theorem original_internal_pair_adjoin_top :
    IntermediateField.adjoin L ({jOver N L, jNOver N L} : Set (modularFunctionFieldOver N L)) = ⊤ := by
  apply IntermediateField.map_injective (modularFunctionFieldOver N L).val
  calc
    (IntermediateField.adjoin L ({jOver N L, jNOver N L} : Set (modularFunctionFieldOver N L))).map
        (modularFunctionFieldOver N L).val =
        IntermediateField.adjoin L ((modularFunctionFieldOver N L).val '' {jOver N L, jNOver N L}) :=
      IntermediateField.adjoin_map L _ (modularFunctionFieldOver N L).val
    _ = IntermediateField.adjoin L ({coeffEmb L jq, coeffEmb L (qExpand ℚ N jq)} : Set (LaurentSeries L)) := by
      rw [Set.image_insert_eq, Set.image_singleton]
      rfl
    _ = modularFunctionFieldOver N L := (original_field_eq_pair_over N L).symm
    _ = (⊤ : IntermediateField L (modularFunctionFieldOver N L)).map
        (modularFunctionFieldOver N L).val :=
      (IntermediateField.fieldRange_val (S := modularFunctionFieldOver N L)).symm.trans
        (AlgHom.fieldRange_eq_map (modularFunctionFieldOver N L).val)

end
end Dubon2026.SourceFunctionField
