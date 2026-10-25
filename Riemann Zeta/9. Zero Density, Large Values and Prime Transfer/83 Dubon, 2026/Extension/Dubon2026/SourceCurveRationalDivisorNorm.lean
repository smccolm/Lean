import Dubon2026.SourceCurveRationalDivisorEvaluation
import Dubon2026.SourceCurveFieldNormEvaluation
import Dubon2026.SourceCurvePullbackEvaluationProduct
import Dubon2026.SourceCurvePicardPushforward
import Dubon2026.SourceCurveEvaluationRestriction
import Dubon2026.SourceFiniteDivisorEvaluationPushforward

/-! DUB-17/18 -> Kummer detection -> evaluation and actual norm transfer.
The previously proved local norm fiber formula and finite-product expansion
supply pullback adjunction. Residue restriction supplies pushforward adjunction. -/
namespace Dubon2026.SourceCurve
noncomputable section
variable {K F E : Type*} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
variable [FiniteDimensional F E] [Algebra.IsSeparable F E]
variable (hbase : ∀ v : Place K F, Function.Bijective (algebraMap K v.ResidueField))
variable (htop : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField))

theorem rationalDivisorEval_finitePullback (D : Divisor K F) (f : E)
    (hord : ∀ v ∈ D.support, ∀ w : Place K E, w.restrict F = v → 0 ≤ w.ord f) :
    rationalDivisorEval htop f (Divisor.finitePullback E D) =
      rationalDivisorEval hbase (Algebra.norm F f) D := by
  change (Divisor.finitePullback E D).prod (fun w n => w.rationalEval (htop w) f ^ n) = _
  rw [Divisor.finitePullback_prod_zpow]
  apply Finset.prod_congr rfl
  intro v hv
  exact congrArg (fun a : K => a ^ D v)
    (v.rationalEval_norm_eq_finprod_fiber (hbase v) htop (hord v hv)).symm

omit [FiniteDimensional F E] in
theorem rationalDivisorEval_geometricPushforward (D : Divisor K E) (f : F) (hf : f ≠ 0)
    (hord : ∀ w ∈ D.support, w.ord (algebraMap F E f) = 0) :
    rationalDivisorEval hbase f (Divisor.geometricPushforward F D) =
      rationalDivisorEval htop (algebraMap F E f) D := by
  have hn (w : Place K E) (hw : w ∈ D.support) :
      (w.restrict F).rationalEval (hbase (w.restrict F)) f ≠ 0 := by
    rw [← w.rationalEval_algebraMap_restrict (hbase (w.restrict F)) (htop w) f]
    exact w.rationalEval_ne_zero_of_ord_eq_zero (htop w)
      ((map_ne_zero (algebraMap F E)).mpr hf) (hord w hw)
  change (D.mapDomain (fun w : Place K E => w.restrict F)).prod
    (fun v n => v.rationalEval (hbase v) f ^ n) = _
  rw [finsupp_prod_zpow_mapDomain _ _ _ hn]
  apply Finsupp.prod_congr
  intro w _
  rw [w.rationalEval_algebraMap_restrict (hbase (w.restrict F)) (htop w) f]

end
end Dubon2026.SourceCurve
