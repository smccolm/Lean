import Dubon2026.SourceRationalPointOrders
import Dubon2026.SourceCurveRationalFunctionEvaluation
import Dubon2026.SourceCurveRationalExtensionDivisors

/-! DUB-17/18 -> original Weil reciprocity -> rational-coordinate reciprocity.
Use the existing rational-extension residue theorem for actual evaluation;
the polynomial center calculation identifies its value at each finite point. -/
namespace Dubon2026.SourceCurve.RationalFunction
noncomputable section
open Polynomial
open scoped Classical
variable (K : Type*) [Field K] [IsAlgClosed K]

/-- Actual residue evaluation on the rational curve, with zero at poles. -/
def placeEval (v : Place K (RatFunc K)) (f : RatFunc K) : K :=
  v.rationalEval (rational_extension_place_residue_bijective K (RatFunc K) v) f

theorem placeEval_polynomial (a : K) (q : K[X]) :
    placeEval K (pointPlace K a) (algebraMap K[X] (RatFunc K) q) = q.eval a := by
  let v := pointPlace K a
  let hv := rational_extension_place_residue_bijective K (RatFunc K) v
  have hm := Place.algebraMap_mem_ofHeightOneSpectrum (K := K) (F := RatFunc K)
    (pointPrime K a)
  have hc := v.sub_rationalRegularEval_mem_center hv hm q
  dsimp only [v, pointPlace] at hc
  rw [Place.center_ofHeightOneSpectrum] at hc
  change q - C (v.rationalRegularEval hv ⟨algebraMap K[X] (RatFunc K) q, hm q⟩) ∈
    Ideal.span {X - C a} at hc
  rw [Ideal.mem_span_singleton, dvd_iff_isRoot, IsRoot.def] at hc
  simp only [eval_sub, eval_C, sub_eq_zero] at hc
  exact (v.rationalEval_of_mem hv (hm q)).trans hc.symm

theorem placeEval_algebraMap (v : Place K (RatFunc K)) (a : K) :
    placeEval K v (algebraMap K (RatFunc K) a) = a :=
  v.rationalEval_algebraMap _ a

theorem placeEval_X (a : K) : placeEval K (pointPlace K a) RatFunc.X = a := by
  simpa only [RatFunc.algebraMap_X, eval_X] using placeEval_polynomial K a X

theorem pointPlace_injective : Function.Injective (pointPlace K) := by
  intro a b h
  have he := congrArg (fun v => placeEval K v RatFunc.X) h
  simpa only [placeEval_X] using he

end
end Dubon2026.SourceCurve.RationalFunction
