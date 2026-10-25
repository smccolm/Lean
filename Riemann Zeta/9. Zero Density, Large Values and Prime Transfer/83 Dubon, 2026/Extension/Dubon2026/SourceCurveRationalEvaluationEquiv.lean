import Dubon2026.SourceCurveRationalEvaluationLaws
import Dubon2026.SourceCurvePlaceTransport

/-! DUB-17/18 -> Kummer detecting divisor -> evaluation of its point difference.
Reuse actual normalized-order transport and residue uniqueness to compare
the evaluations under a constant-preserving field equivalence. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
variable {K F E : Type*} [Field K] [Field F] [Field E] [Algebra K F] [Algebra K E]

theorem rationalEval_comapEquiv_of_mem (w : Place K E) (e : F ≃ₐ[K] E)
    (hw : Function.Bijective (algebraMap K w.ResidueField))
    (he : Function.Bijective (algebraMap K (w.comapEquiv e).ResidueField))
    (f : F) (hf : e f ∈ w.toValuationSubring) :
    (w.comapEquiv e).rationalEval he f = w.rationalEval hw (e f) := by
  classical
  let c := w.rationalEval hw (e f)
  by_cases hz : e f - algebraMap K E c = 0
  · have heq : f = algebraMap K F c := e.injective (by
      rw [e.commutes]
      exact sub_eq_zero.mp hz)
    rw [heq, e.commutes, rationalEval_algebraMap, rationalEval_algebraMap]
  · have hv : w.rationalEval hw (e f - algebraMap K E c) = 0 := by
      rw [w.rationalEval_sub_algebraMap hw hf]
      exact sub_self _
    have ho := (w.rationalEval_eq_zero_iff_ord_pos hw
      (sub_mem hf (w.algebraMap_mem' c)) hz).mp hv
    apply (w.comapEquiv e).rationalEval_eq_of_ord_sub_pos he
    rw [ord_comapEquiv, map_sub, e.commutes]
    exact ho

end
end Dubon2026.SourceCurve.Place
