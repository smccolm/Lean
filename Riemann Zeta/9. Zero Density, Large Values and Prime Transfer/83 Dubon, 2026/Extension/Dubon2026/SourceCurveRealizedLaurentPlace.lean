import Dubon2026.SourceCurveNormalizedLaurentPlace
import Dubon2026.SourceAnalyticLaurentQuotients

/-! DUB-17/18 -> every actual Kummer place -> normalized local realization.
Assemble the existing convergent-field embedding and normalized Laurent-place
construction before instantiating the literal original function field. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open SourceFunctionField.CuspTaylor
variable {F E : Type*} [Field F] [Field E] [Algebra ℂ F] [Algebra ℂ E]
variable [Algebra F E] [IsScalarTower ℂ F E] [Algebra.IsIntegral F E]

theorem exists_place_of_realized_laurent_extension
    (ι : F →ₐ[ℂ] realizedField) (v : Place ℂ F)
    (hv : ∀ g : F, g ≠ 0 → (ι g).val.order = v.ord g)
    (hex : ∃ e : E →ₐ[ℂ] realizedField, ∀ g : F, e (algebraMap F E g) = ι g) :
    ∃ (w : Place ℂ E) (e : E →ₐ[ℂ] realizedField), w.restrict F = v ∧
      (∀ g : F, e (algebraMap F E g) = ι g) ∧ ∀ a : E, w.ord a = (e a).val.order := by
  obtain ⟨e, he⟩ := hex
  obtain ⟨w, hw, ho⟩ := exists_place_of_laurent_extension
    (realizedField.val.comp ι) (realizedField.val.comp e) v
    (fun g => congrArg Subtype.val (he g)) hv
  exact ⟨w, e, hw, he, ho⟩

end
end Dubon2026.SourceCurve.Place
