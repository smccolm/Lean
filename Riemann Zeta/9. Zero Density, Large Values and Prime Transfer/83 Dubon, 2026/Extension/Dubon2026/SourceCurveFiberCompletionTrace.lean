import Dubon2026.SourceCurveFiberCompletionProduct
import Dubon2026.SourceCurveProductFieldTrace

/-! The field trace is the sum of the traces in all actual completions
above a place. The product isomorphism, its embedding formula, and its
degree hypotheses are proved upstream. This is the remaining algebraic
assembly needed to sum local Tate identities in the DUB-17/18 residue
theorem dependency. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

open scoped TensorProduct

variable {K F E : Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [Algebra.IsIntegral F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
  (v : Place K F)

/-- The original trace equals the sum of actual local completion traces over the restriction fiber. -/
theorem completionTraceSum
    (hbase : Function.Bijective (algebraMap K v.ResidueField))
    (htop : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField)) (g : E) :
    algebraMap F v.adicCompletion (Algebra.trace F E g) =
      ∑ᶠ w : {w : Place K E // w.restrict F = v},
        Algebra.trace v.adicCompletion w.1.adicCompletion
          (algebraMap E w.1.adicCompletion g) := by
  classical
  letI := Fintype.ofFinite {w : Place K E // w.restrict F = v}
  rw [finsum_eq_sum_of_fintype,
    algebraTrace_product_decomposition F v.adicCompletion E
      (fun w : {w : Place K E // w.restrict F = v} => w.1.adicCompletion)
      (v.fiberCompletionProduct hbase htop) g]
  exact Finset.sum_congr rfl fun w _ =>
    congrArg (Algebra.trace v.adicCompletion w.1.adicCompletion)
      (v.fiberCompletionProduct_one_tmul hbase htop g w)

end Dubon2026.SourceCurve.Place
