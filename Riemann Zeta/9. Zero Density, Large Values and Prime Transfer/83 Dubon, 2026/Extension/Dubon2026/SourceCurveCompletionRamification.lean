import Dubon2026.SourceCurveCompletionIdealPowers
import Dubon2026.SourceCurveCompletionIntegralAlgebra
import Mathlib.NumberTheory.RamificationInertia.Basic

/-! Completion preserves the original ramification index. The original
base uniformizer generates the completed maximal ideal, and the proved
valuation law identifies its exact power in the extension. This supplies
the ramification factor in the dimension formula needed for the DUB-17/18
sum of completed field traces over places. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

open IsLocalRing WithZero

variable {K F E : Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [Algebra.IsIntegral F E] (w : Place K E)

/-- The image of the completed base uniformizer has the original ramification valuation. -/
theorem valued_completion_base_uniformizer :
    Valued.v ((algebraMap (w.restrict F).adicCompletionIntegers w.adicCompletionIntegers
      (w.restrict F).completionUniformizer : w.adicCompletionIntegers) : w.adicCompletion) =
        exp (-(w.ramificationIndex (F := F) : ℤ)) := by
  change Valued.v (w.adicCompletionComap (F := F)
    ((w.restrict F).completionUniformizer : (w.restrict F).adicCompletion)) = _
  rw [w.valued_adicCompletionComap, (w.restrict F).valued_completionUniformizer, ← exp_nsmul]
  simp only [nsmul_eq_mul, mul_neg_one]

/-- The native ramification index of the completed integral rings is the original index. -/
theorem completion_ramificationIdx :
    (maximalIdeal (w.restrict F).adicCompletionIntegers).ramificationIdx
      (maximalIdeal w.adicCompletionIntegers) = w.ramificationIndex (F := F) := by
  have hmap : (maximalIdeal (w.restrict F).adicCompletionIntegers).map
      (algebraMap (w.restrict F).adicCompletionIntegers w.adicCompletionIntegers) =
      Ideal.span {algebraMap (w.restrict F).adicCompletionIntegers w.adicCompletionIntegers
        (w.restrict F).completionUniformizer} := by
    rw [(w.restrict F).completion_maximalIdeal_eq_span, Ideal.map_span, Set.image_singleton]
  apply Ideal.ramificationIdx_spec
  · rw [hmap, Ideal.span_singleton_le_iff_mem, w.mem_completion_maximalIdeal_pow,
      w.valued_completion_base_uniformizer]
  · rw [hmap, Ideal.span_singleton_le_iff_mem, w.mem_completion_maximalIdeal_pow,
      w.valued_completion_base_uniformizer]
    change ¬ (↑(Multiplicative.ofAdd (-(w.ramificationIndex (F := F) : ℤ))) : ℤᵐ⁰) ≤
      (↑(Multiplicative.ofAdd (-((w.ramificationIndex (F := F) + 1 : ℕ) : ℤ))) : ℤᵐ⁰)
    simp only [WithZero.coe_le_coe, Multiplicative.ofAdd_le, not_le]
    omega

end Dubon2026.SourceCurve.Place
