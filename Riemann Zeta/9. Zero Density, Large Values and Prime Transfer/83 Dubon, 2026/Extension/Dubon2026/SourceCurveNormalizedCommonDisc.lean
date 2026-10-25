import Dubon2026.SourceCurveConvergentCommonDisc
import Dubon2026.SourceCurvePlaces

/-! DUB-17/18 -> auxiliary Kummer point division -> analytic cover charts.
A finite coordinate and a convergent embedding matching the actual place orders
supply a common positive disk with those normalized orders at the center. -/
namespace Dubon2026.SourceFunctionField.CuspTaylor
noncomputable section
open SourceCurve Metric IntermediateField

theorem exists_normalized_common_disc {E : Type*} [Field E] [Algebra ℂ E]
    (t : E) [FiniteDimensional ℂ⟮t⟯ E] (w : Place ℂ E)
    (e : E →ₐ[ℂ] realizedField) (ho : ∀ a : E, w.ord a = (e a).val.order) :
    ∃ R : ℝ, 0 < R ∧ ∀ a : E, ∃ G : ℂ → ℂ,
      MeromorphicOn G (ball 0 R) ∧ Represents (e a).val G ∧
      (a ≠ 0 → meromorphicOrderAt G 0 = (w.ord a : WithTop ℤ)) ∧
      (a ≠ 0 → ∀ z ∈ ball 0 R, meromorphicOrderAt G z ≠ ⊤) := by
  obtain ⟨R, hR, hG⟩ := exists_common_disc_of_finite_coordinate t e
  refine ⟨R, hR, fun a => ?_⟩
  obtain ⟨G, hm, hr⟩ := hG a
  have hne (ha : a ≠ 0) : (e a).val ≠ 0 :=
    (map_ne_zero (realizedField.val.comp e)).mpr ha
  exact ⟨G, hm, hr, fun ha => (hr.order (hne ha)).trans (congrArg _ (ho a).symm),
    fun ha z hz => order_ne_top_on_disc hR hm hr (hne ha) hz⟩

theorem exists_normalized_common_disc_with {E : Type*} [Field E] [Algebra ℂ E]
    (t : E) (ht : FiniteDimensional ℂ⟮t⟯ E) (w : Place ℂ E)
    (P : (E →ₐ[ℂ] realizedField) → Prop)
    (hex : ∃ e : E →ₐ[ℂ] realizedField, P e ∧ ∀ a : E, w.ord a = (e a).val.order) :
    ∃ (e : E →ₐ[ℂ] realizedField) (R : ℝ), 0 < R ∧ P e ∧
      ∀ a : E, ∃ G : ℂ → ℂ,
        MeromorphicOn G (ball 0 R) ∧ Represents (e a).val G ∧
        (a ≠ 0 → meromorphicOrderAt G 0 = (w.ord a : WithTop ℤ)) ∧
        (a ≠ 0 → ∀ z ∈ ball 0 R, meromorphicOrderAt G z ≠ ⊤) := by
  letI := ht
  obtain ⟨e, he, ho⟩ := hex
  obtain ⟨R, hR, hG⟩ := exists_normalized_common_disc t w e ho
  exact ⟨e, R, hR, he, hG⟩

end
end Dubon2026.SourceFunctionField.CuspTaylor
