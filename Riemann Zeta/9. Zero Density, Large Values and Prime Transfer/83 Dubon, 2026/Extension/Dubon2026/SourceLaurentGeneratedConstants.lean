import Dubon2026.SourceLaurentConstantTranscendence

/-! DUB-17/18 -> rational Fourier spanning -> integral base change of Fricke
fractions. The coefficient embedding is a field map. Thus the field generated
by cyclotomic Laurent series still has coefficients in the same field, and
constant transcendence supplies the exact relative premise used by the proved
transcendental constant-adjoining span theorem. -/
namespace Dubon2026.SourceFricke.ConstantDescent
noncomputable section
open Dubon2026.SourceFunctionField

variable (F : IntermediateField ℚ ℂ)

theorem constant_mem_coeffMap_fieldRange (a : F) :
    algebraMap F (LaurentSeries ℂ) a ∈ (coeffMap (algebraMap F ℂ)).fieldRange := by
  refine ⟨algebraMap F (LaurentSeries F) a, ?_⟩
  rw [SourceDifferential.algebraMap_laurentSeries_apply_alt, coeffMap_single]
  change HahnSeries.single 0 (a : ℂ) = algebraMap ℂ (LaurentSeries ℂ) (a : ℂ)
  exact (SourceDifferential.algebraMap_laurentSeries_apply_alt ℂ (a : ℂ)).symm

theorem generated_mem_coeffMap_fieldRange {S : Set (LaurentSeries ℂ)}
    (hS : S ⊆ (coeffMap (algebraMap F ℂ)).fieldRange) {z : LaurentSeries ℂ}
    (hz : z ∈ KFld F S) : z ∈ (coeffMap (algebraMap F ℂ)).fieldRange := by
  rw [← IntermediateField.mem_toSubfield, IntermediateField.adjoin_toSubfield] at hz
  refine Subfield.closure_le (t := (coeffMap (algebraMap F ℂ)).fieldRange) |>.mpr ?_ hz
  rintro w (⟨a, rfl⟩ | hw)
  · exact constant_mem_coeffMap_fieldRange F a
  · exact hS hw

theorem generated_coeff_mem {S : Set (LaurentSeries ℂ)}
    (hS : S ⊆ (coeffMap (algebraMap F ℂ)).fieldRange) {z : LaurentSeries ℂ}
    (hz : z ∈ KFld F S) (m : ℤ) : z.coeff m ∈ F := by
  obtain ⟨y, rfl⟩ := generated_mem_coeffMap_fieldRange F hS hz
  exact (y.coeff m).property

theorem constant_transcendental_generated {S : Set (LaurentSeries ℂ)}
    {t : LaurentSeries ℂ} (htS : t ∈ S)
    (hS : S ⊆ (coeffMap (algebraMap F ℂ)).fieldRange)
    {c : ℂ} (hc : Transcendental F c) :
    Transcendental (KFldT F t S) (algebraMap ℂ (LaurentSeries ℂ) c) := by
  apply constant_transcendental_of_coeff_mem F (KFldT F t S).toSubfield _ hc
  intro z hz m
  exact generated_coeff_mem F hS ((mem_KFldT_iff F t S htS z).mp hz) m

/-- Extending the constant field preserves the literal coefficient-map range. -/
theorem coeffMap_fieldRange_mono {G : IntermediateField ℚ ℂ} (h : F ≤ G)
    {S : Set (LaurentSeries ℂ)} (hS : S ⊆ (coeffMap (algebraMap F ℂ)).fieldRange) :
    S ⊆ (coeffMap (algebraMap G ℂ)).fieldRange := by
  intro z hz
  obtain ⟨y, hy⟩ := hS hz
  refine ⟨coeffMap (IntermediateField.inclusion h).toRingHom y, ?_⟩
  rw [coeffMap_coeffMap]
  have he : (algebraMap G ℂ).comp (IntermediateField.inclusion h).toRingHom =
      algebraMap F ℂ := by
    ext a
    rfl
  rw [he]
  exact hy
end
end Dubon2026.SourceFricke.ConstantDescent