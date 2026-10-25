import Dubon2026.SourceCurveRealizedLaurentPlace
import Dubon2026.SourceCurveGaloisFiberTransitivity
import Dubon2026.SourceCurveCompletionEmbeddingValuation

/-! DUB-17/18 -> actual torsion-cover charts -> every place in a Galois fiber.
Transport the normalized convergent embedding using native place transitivity.
This supplies the exact local order comparison required by the cover charts. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open SourceFunctionField.CuspTaylor
variable {F E : Type*} [Field F] [Field E] [Algebra ℂ F] [Algebra ℂ E]
variable [Algebra F E] [IsScalarTower ℂ F E] [FiniteDimensional F E] [IsGalois F E]

theorem exists_normalized_convergent_embedding (w : Place ℂ E)
    (ι : F →ₐ[ℂ] realizedField)
    (hex : ∃ (w₀ : Place ℂ E) (e : E →ₐ[ℂ] realizedField),
      w₀.restrict F = w.restrict F ∧
      (∀ g : F, e (algebraMap F E g) = ι g) ∧
      ∀ a : E, w₀.ord a = (e a).val.order) :
    ∃ e : E →ₐ[ℂ] realizedField,
      (∀ g : F, e (algebraMap F E g) = ι g) ∧
      ∀ a : E, w.ord a = (e a).val.order := by
  obtain ⟨w₀, e, hw₀, he, ho⟩ := hex
  obtain ⟨σ, hσ⟩ := w₀.exists_comapEquiv_of_restrict_eq w hw₀.symm
  refine ⟨e.comp (σ.restrictScalars ℂ).toAlgHom, ?_, ?_⟩
  · intro g
    change e (σ (algebraMap F E g)) = _
    rw [σ.commutes, he]
  · intro a
    change w.ord a = (e (σ a)).val.order
    rw [← hσ, Place.ord_comapEquiv]
    exact ho (σ a)

end
end Dubon2026.SourceCurve.Place
