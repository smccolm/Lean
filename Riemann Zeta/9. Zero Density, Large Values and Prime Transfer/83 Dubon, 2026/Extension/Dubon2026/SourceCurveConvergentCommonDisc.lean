import Dubon2026.SourceCuspDiscRealization
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-! DUB-17/18 -> auxiliary torsion-cover charts -> one common local disk.
The actual finite-coordinate cover is finitely generated as a field over C.
Its finitely many convergent Laurent generators have a common positive disk;
the existing disk intermediate field then contains every field element. -/
namespace Dubon2026.SourceFunctionField.CuspTaylor
noncomputable section
open IntermediateField Metric

theorem exists_common_disc_of_generators {E : Type*} [Field E] [Algebra ℂ E]
    (e : E →ₐ[ℂ] realizedField) (s : Finset E) (hs : adjoin ℂ (s : Set E) = ⊤) :
    ∃ R : ℝ, 0 < R ∧ ∀ a : E, ∃ G : ℂ → ℂ,
      MeromorphicOn G (ball 0 R) ∧ Represents (e a).val G := by
  classical
  have hex (t : Finset E) : ∃ R : ℝ, 0 < R ∧ ∀ a ∈ t, (e a).val ∈ discField R := by
    induction t using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, fun _ h => (Finset.notMem_empty _ h).elim⟩
    | @insert a t _ ih =>
      obtain ⟨r, hr, ha⟩ := exists_discField_of_realized (e a).property
      obtain ⟨u, hu, ht⟩ := ih
      refine ⟨min r u, lt_min hr hu, ?_⟩
      intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact discField_mono (min_le_left r u) ha
      · exact discField_mono (min_le_right r u) (ht b hb)
  obtain ⟨R, hR, hgen⟩ := hex s
  have hle : adjoin ℂ (s : Set E) ≤ (discField R).comap (realizedField.val.comp e) :=
    adjoin_le_iff.mpr hgen
  refine ⟨R, hR, fun a => ?_⟩
  exact hle (hs ▸ IntermediateField.mem_top)

theorem exists_common_disc_of_finite_coordinate {E : Type*} [Field E] [Algebra ℂ E]
    (t : E) [FiniteDimensional ℂ⟮t⟯ E] (e : E →ₐ[ℂ] realizedField) :
    ∃ R : ℝ, 0 < R ∧ ∀ a : E, ∃ G : ℂ → ℂ,
      MeromorphicOn G (ball 0 R) ∧ Represents (e a).val G := by
  letI : Algebra.EssFiniteType ℂ ℂ⟮t⟯ :=
    IntermediateField.essFiniteType_iff.mpr (fg_adjoin_of_finite (Set.finite_singleton t))
  letI : Algebra.EssFiniteType ℂ E := Algebra.EssFiniteType.comp ℂ ℂ⟮t⟯ E
  obtain ⟨s, hs⟩ := IntermediateField.fg_top ℂ E
  exact exists_common_disc_of_generators e s hs

end
end Dubon2026.SourceFunctionField.CuspTaylor
