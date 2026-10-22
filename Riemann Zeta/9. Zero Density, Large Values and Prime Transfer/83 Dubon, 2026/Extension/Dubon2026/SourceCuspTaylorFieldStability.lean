import Dubon2026.SourceOriginalJCuspGerm
import Dubon2026.SourceCuspTaylorLaurentSubstitution
import Dubon2026.SourceJPrimeTwistCoordinates

/-! DUB-17/18 -> original torsion cardinality -> cusp parameters.
The actual analytic Taylor quotient field is stable under the same
unit-twist and positive-power maps used by the original cusp embeddings.
Consequently every literal twisted/substituted j generator is realized.
-/
namespace Dubon2026.SourceFunctionField.CuspTaylor
noncomputable section

theorem qTwist_mem_realizedField (u : ℂˣ) {A : LaurentSeries ℂ} (hA : A ∈ realizedField) :
    qTwist u A ∈ realizedField := by
  obtain ⟨f, g, hf, hg, hg0, hAeq⟩ := hA
  have hfc : AnalyticAt ℂ (fun z : ℂ => f (u * z)) 0 := by
    have h : AnalyticAt ℂ f ((u : ℂ) * 0) := by simpa only [mul_zero] using hf
    exact h.comp (analyticAt_const.mul analyticAt_id)
  have hgc : AnalyticAt ℂ (fun z : ℂ => g (u * z)) 0 := by
    have h : AnalyticAt ℂ g ((u : ℂ) * 0) := by simpa only [mul_zero] using hg
    exact h.comp (analyticAt_const.mul analyticAt_id)
  refine ⟨_, _, hfc, hgc, ?_, ?_⟩
  · rw [← qTwist_series u hg]
    exact (map_ne_zero (qTwist u)).mpr hg0
  · rw [hAeq, map_div₀, qTwist_series u hf, qTwist_series u hg]

theorem qExpand_mem_realizedField (d : ℕ) [NeZero d]
    {A : LaurentSeries ℂ} (hA : A ∈ realizedField) : qExpand ℂ d A ∈ realizedField := by
  obtain ⟨f, g, hf, hg, hg0, hAeq⟩ := hA
  have hfc : AnalyticAt ℂ (fun z : ℂ => f (z ^ d)) 0 := by
    have h : AnalyticAt ℂ f ((0 : ℂ) ^ d) := by simpa only [zero_pow (NeZero.ne d)] using hf
    exact AnalyticAt.comp (f := fun z : ℂ => z ^ d) h (analyticAt_id.pow d)
  have hgc : AnalyticAt ℂ (fun z : ℂ => g (z ^ d)) 0 := by
    have h : AnalyticAt ℂ g ((0 : ℂ) ^ d) := by simpa only [zero_pow (NeZero.ne d)] using hg
    exact AnalyticAt.comp (f := fun z : ℂ => z ^ d) h (analyticAt_id.pow d)
  refine ⟨_, _, hfc, hgc, ?_, ?_⟩
  · rw [← qExpand_series d hg]
    exact (map_ne_zero (qExpand ℂ d)).mpr hg0
  · rw [hAeq, map_div₀, qExpand_series d hf, qExpand_series d hg]

theorem TS_mem_realizedField (d : ℕ) [NeZero d] (u : ℂˣ) :
    PrimeDegreeAux.TS ℂ d u ∈ realizedField :=
  qExpand_mem_realizedField d (qTwist_mem_realizedField u jqModC_mem_realizedField)

end
end Dubon2026.SourceFunctionField.CuspTaylor
