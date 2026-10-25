import Dubon2026.SourceCurveAnalyticPlaceParameter
import Dubon2026.SourceCurveConvergentEvaluationFamily

/-! DUB-17/18 -> auxiliary Kummer point division -> actual analytic cover charts.
Consume the proved convergent place family: residue values, normalized orders,
and the order-one uniformizer derive every input to the analytic inversion.
The resulting parameter family is injective and preserves the actual orders. -/
namespace Dubon2026.SourceCurve.AnalyticDisc
noncomputable section
open SourceFunctionField.CuspTaylor Metric

theorem exists_parameter_of_convergent_family {E : Type*} [Field E] [Algebra ℂ E]
    (e : E →ₐ[ℂ] realizedField) {R δ : ℝ} (hR : 0 < R) (G : E → ℂ → ℂ)
    (hm : ∀ a, MeromorphicOn (G a) (ball 0 R))
    (hr : ∀ a, Represents (e a).val (G a))
    (hv : ∀ P : Place ℂ E, Function.Bijective (algebraMap ℂ P.ResidueField))
    (w : Place ℂ E) (hδ : 0 < δ) (γ : ℂ → Place ℂ E) (hγ0 : γ 0 = w)
    (hball : ∀ (z : ℂ), z ∈ ball 0 δ → z ∈ ball 0 R)
    (hmem : ∀ z ∈ ball 0 δ, ∀ a,
      a ∈ (γ z).toValuationSubring ↔ 0 ≤ meromorphicOrderAt (G a) z)
    (horder : ∀ z ∈ ball 0 δ, ∀ a, a ≠ 0 →
      meromorphicOrderAt (G a) z = ((γ z).ord a : WithTop ℤ)) :
    ∃ (ρ : ℝ) (η : ℂ → Place ℂ E), 0 < ρ ∧ η 0 = w ∧ Set.InjOn η (ball 0 ρ) ∧
      (∀ z ∈ ball 0 ρ, (η z).rationalEval (hv (η z)) w.uniformizer = z) ∧
      ∀ z ∈ ball 0 ρ, ∀ a : E, a ≠ 0 →
        MeromorphicAt (fun t => (η t).rationalEval (hv (η t)) a) z ∧
        meromorphicOrderAt (fun t => (η t).rationalEval (hv (η t)) a) z =
          ((η z).ord a : WithTop ℤ) ∧
        (a ∈ (η z).toValuationSubring →
          AnalyticAt ℂ (fun t => (η t).rationalEval (hv (η t)) a) z) := by
  have ho : meromorphicOrderAt (G w.uniformizer) 0 = (1 : ℤ) := by
    rw [horder 0 (mem_ball_self hδ) _ w.uniformizer_ne_zero, hγ0, w.ord_uniformizer]
  obtain ⟨hT, hT0, hd⟩ := normal_uniformizer hR G hm w ho
  apply exists_parameter_of_evaluation_family hv w (normal R G w.uniformizer)
    hT hT0 hd hδ γ hγ0
  · intro z hz
    exact rationalEval_eq_normal e hR G hm hr (hball z hz) (γ z) (hv (γ z))
      (hmem z hz) (horder z hz) w.uniformizer
  · intro z hz a ha
    exact evaluation_orders e hR G hm hr hv γ hball hmem horder a ha hz

end
end Dubon2026.SourceCurve.AnalyticDisc
