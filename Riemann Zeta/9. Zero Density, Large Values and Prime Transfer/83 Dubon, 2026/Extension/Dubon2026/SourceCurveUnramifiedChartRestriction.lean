import Dubon2026.SourceCurveAnalyticChartOrders
import Dubon2026.SourceCurveEvaluationRestriction
import Dubon2026.SourceCurveCompletionEmbeddingValuation

/-! DUB-17/18 -> auxiliary compactness -> actual restriction charts.
Restriction preserves all normalized meromorphic reading orders when its
ramification index is one. The readings use the native residue map.
-/
namespace Dubon2026.SourceCurve.AnalyticChart
noncomputable section
variable {F E : Type*} [Field F] [Field E]
variable [Algebra ℂ F] [Algebra ℂ E] [Algebra F E] [IsScalarTower ℂ F E]
variable [Algebra.IsIntegral F E]

theorem Orders.restrict_unramified
    (hF : ∀ v : Place ℂ F, Function.Bijective (algebraMap ℂ v.ResidueField))
    (hE : ∀ w : Place ℂ E, Function.Bijective (algebraMap ℂ w.ResidueField))
    (hunram : ∀ w : Place ℂ E, w.ramificationIndex (F := F) = 1)
    {γ : ℂ → Place ℂ E} {U : Set ℂ} (hγ : Orders hE γ U) :
    Orders hF (fun z => (γ z).restrict F) U := by
  intro z hz a ha
  have ham : algebraMap F E a ≠ 0 := (map_ne_zero (algebraMap F E)).mpr ha
  have h := hγ z hz (algebraMap F E a) ham
  have heq : (fun t => (γ t).rationalEval (hE (γ t)) (algebraMap F E a)) =
      (fun t => ((γ t).restrict F).rationalEval (hF ((γ t).restrict F)) a) := by
    funext t
    exact (γ t).rationalEval_algebraMap_restrict (hF _) (hE _) a
  rw [heq] at h
  have ho : (γ z).ord (algebraMap F E a) = ((γ z).restrict F).ord a := by
    rw [(γ z).ord_algebraMap_restrict, ← (γ z).ramificationIndex_cast, hunram,
      Nat.cast_one, mul_one]
  exact ⟨h.1, h.2.1.trans (congrArg (fun k : ℤ => (k : WithTop ℤ)) ho),
    fun hm => h.2.2 ((γ z).mem_restrict_iff.mp hm)⟩

end
end Dubon2026.SourceCurve.AnalyticChart
