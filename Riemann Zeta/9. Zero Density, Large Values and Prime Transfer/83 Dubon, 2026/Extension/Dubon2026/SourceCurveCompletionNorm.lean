import Dubon2026.SourceCurveCompletionFinite

/-! The actual complete discrete valuation supplies a normalized absolute
value extending that on the base completion. This is the precise input to
native spectral-norm integrality, hence to the finite integral basis used
by the local residue/field-trace comparison (DUB-17/18 reverse genus).
Adapted from the verified FLT completion trace source; native rank-one
valuation and norm theorems discharge the normalization. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

open WithZero WithZeroMulInt Valuation.IsRankOneDiscrete
open scoped Valued NNReal

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

/-- The actual completed discrete valuation, embedded in positive real values with base two. -/
@[implicit_reducible]
def completionRankOne : (Valued.v : Valuation v.adicCompletion ℤᵐ⁰).RankOne := by
  letI := v.completionValuation_nontrivial
  exact Valuation.IsRankOneDiscrete.rankOne _ (one_lt_two (α := ℝ≥0))

/-- The chosen norm is exactly the base-two norm of the normalized integer valuation. -/
theorem completion_norm_eq (x : v.adicCompletion) :
    letI := v.completionRankOne
    ‖x‖ = (WithZeroMulInt.toNNReal (two_ne_zero) (Valued.v x) : ℝ) := by
  letI := v.completionRankOne
  have h := valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
    (v.heightOneSpectrum.valuedAdicCompletion_surjective F) x
  simp only [Valued.toNormedField.norm_def, Valuation.RankOne.hom]
  rw [← h]
  rfl

variable {E : Type*} [Field E] [Algebra K E] [Algebra F E]
  [IsScalarTower K F E] [Algebra.IsIntegral F E] (w : Place K E)

/-- Renormalize the actual extension norm by its proved positive ramification index. -/
def completionRelativeAbsoluteValue : AbsoluteValue w.adicCompletion ℝ :=
  letI := w.completionRankOne
  have hr : (0 : ℝ) < ((w.ramificationIndex (F := F) : ℝ))⁻¹ :=
    inv_pos.mpr (Nat.cast_pos.mpr (w.ramificationIndex_pos (F := F)))
  { toFun := fun y => ‖y‖ ^ ((w.ramificationIndex (F := F) : ℝ))⁻¹
    map_mul' := fun x y => by rw [norm_mul, Real.mul_rpow (norm_nonneg x) (norm_nonneg y)]
    nonneg' := fun x => Real.rpow_nonneg (norm_nonneg _) _
    eq_zero' := fun x => by
      rw [Real.rpow_eq_zero_iff_of_nonneg (norm_nonneg x), norm_eq_zero]
      exact ⟨fun h => h.1, fun h => ⟨h, hr.ne'⟩⟩
    add_le' := fun x y => by
      have hmax : ‖x + y‖ ≤ max ‖x‖ ‖y‖ := Valuation.norm_add_le Valued.v x y
      refine (Real.rpow_le_rpow (norm_nonneg _) hmax hr.le).trans ?_
      rcases max_cases ‖x‖ ‖y‖ with ⟨hm, _⟩ | ⟨hm, _⟩ <;> rw [hm]
      · exact le_add_of_nonneg_right (Real.rpow_nonneg (norm_nonneg _) _)
      · exact le_add_of_nonneg_left (Real.rpow_nonneg (norm_nonneg _) _) }

/-- The renormalized extension absolute value restricts exactly to the actual base norm. -/
theorem completionRelativeAbsoluteValue_extends (c : (w.restrict F).adicCompletion) :
    letI := (w.restrict F).completionRankOne
    w.completionRelativeAbsoluteValue (F := F) (algebraMap (w.restrict F).adicCompletion w.adicCompletion c) =
      ‖c‖ := by
  letI := (w.restrict F).completionRankOne
  letI := w.completionRankOne
  have hr : (0 : ℝ) < (w.ramificationIndex (F := F) : ℝ) :=
    Nat.cast_pos.mpr (w.ramificationIndex_pos (F := F))
  change ‖algebraMap (w.restrict F).adicCompletion w.adicCompletion c‖ ^
    ((w.ramificationIndex (F := F) : ℝ))⁻¹ = ‖c‖
  rw [w.completion_norm_eq, (w.restrict F).completion_norm_eq,
    w.algebraMap_completionExtension, w.valued_adicCompletionComap, map_pow, NNReal.coe_pow,
    ← Real.rpow_natCast, ← Real.rpow_mul (NNReal.coe_nonneg _), mul_inv_cancel₀ hr.ne', Real.rpow_one]

end Dubon2026.SourceCurve.Place
