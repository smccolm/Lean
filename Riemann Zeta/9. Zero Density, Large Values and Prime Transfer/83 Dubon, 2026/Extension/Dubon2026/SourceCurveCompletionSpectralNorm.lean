import Dubon2026.SourceCurveCompletionIntegrality
import Dubon2026.SourceCurveFiberCompletions

/-! The unique native spectral norm recovers the original valuation ring
from its completion. Thus two fiber components with the same kernel must
come from the same original place. This supplies the distinct maximal
ideals needed for the DUB-17/18 product-of-completions trace argument. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

open scoped Valued

variable {K F E : Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [Algebra.IsIntegral F E] (w : Place K E)

/-- The normalized extension absolute value detects exactly the actual completed integral ring. -/
theorem completionRelativeAbsoluteValue_le_one_iff (x : w.adicCompletion) :
    w.completionRelativeAbsoluteValue (F := F) x ≤ 1 ↔ x ∈ w.adicCompletionIntegers := by
  letI := w.completionRankOne
  have hr : (0 : ℝ) < ((w.ramificationIndex (F := F) : ℝ))⁻¹ :=
    inv_pos.mpr (Nat.cast_pos.mpr (w.ramificationIndex_pos (F := F)))
  change ‖x‖ ^ ((w.ramificationIndex (F := F) : ℝ))⁻¹ ≤ 1 ↔ Valued.v x ≤ 1
  constructor
  · intro hx
    apply Valued.toNormedField.norm_le_one_iff.mp
    by_contra h
    have hgt : 1 < ‖x‖ := not_le.mp h
    exact (not_lt.mpr hx) ((Real.one_lt_rpow_iff_of_pos (lt_trans zero_lt_one hgt)).mpr
      (Or.inl ⟨hgt, hr⟩))
  · intro hx
    exact Real.rpow_le_one (norm_nonneg _) (Valued.toNormedField.norm_le_one_iff.mpr hx) hr.le

/-- The native spectral norm is the proved ramification-normalized extension absolute value. -/
theorem completion_spectralNorm_eq_relativeAbsoluteValue [FiniteDimensional F E]
    (x : w.adicCompletion) :
    letI := (w.restrict F).completionRankOne
    spectralNorm (w.restrict F).adicCompletion w.adicCompletion x =
      w.completionRelativeAbsoluteValue (F := F) x := by
  letI := (w.restrict F).completionRankOne
  letI : FiniteDimensional (w.restrict F).adicCompletion w.adicCompletion :=
    w.finiteDimensional_completion (F := F)
  letI : Algebra.IsAlgebraic (w.restrict F).adicCompletion w.adicCompletion :=
    Algebra.IsAlgebraic.of_finite _ _
  letI : IsUltrametricDist (w.restrict F).adicCompletion :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (fun a b => Valuation.norm_add_le Valued.v a b)
  exact (spectralNorm_unique_field_norm_ext (f := w.completionRelativeAbsoluteValue (F := F))
    (w.completionRelativeAbsoluteValue_extends (F := F)) x).symm

/-- At a fiber place the common-base spectral norm recovers membership in the original local ring. -/
theorem fiberCompletion_spectralNorm_le_one_iff [FiniteDimensional F E] (v : Place K F)
    (z : {z : Place K E // z.restrict F = v}) (g : E) :
    letI := v.completionRankOne
    spectralNorm v.adicCompletion z.1.adicCompletion
      (algebraMap E z.1.adicCompletion g) ≤ 1 ↔ g ∈ z.1.toValuationSubring := by
  rcases z with ⟨z, hz⟩
  subst v
  letI := (z.restrict F).completionRankOne
  rw [z.completion_spectralNorm_eq_relativeAbsoluteValue,
    z.completionRelativeAbsoluteValue_le_one_iff, z.completion_integer_iff]

end Dubon2026.SourceCurve.Place
