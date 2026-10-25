import Dubon2026.SourceCurvePrimePlaces
import Mathlib.FieldTheory.RatFunc.Valuation

/-! DUB-17/18 -> original Weil reciprocity -> finite norm transfer to
the rational coordinate -> reciprocity with the coordinate X. Its pole is
the actual infinity valuation. Reuse the native normalized-order uniqueness
theorem, so no second normalization argument or general reciprocity induction
is needed here. Adapted from Def_AlgebraicCurve_RatFuncPlaceInfty,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceCurve.RationalFunction
noncomputable section
open WithZero
open scoped Classical
variable (K : Type*) [Field K]

/-- The actual pole place of the rational coordinate. -/
def infinityPlace : Place K (RatFunc K) where
  toValuationSubring := (RatFunc.inftyValuation K).valuationSubring
  algebraMap_mem' a :=
    Valuation.IsTrivialOn.valuation_algebraMap_le_one (v := RatFunc.inftyValuation K) a
  ne_top' := by
    simp only [ne_eq, Valuation.valuationSubring_eq_top_iff, not_not]
    infer_instance
  isPrincipalIdealRing' := Valuation.valuationSubring_isPrincipalIdealRing _

theorem infinityPlace_ord {f : RatFunc K} (hf : f ≠ 0) :
    (infinityPlace K).ord f = -f.intDegree := by
  have hnorm : -log (RatFunc.inftyValuation K f) = (infinityPlace K).ord f := by
    apply Place.eq_ord_of_addHom_of_nonneg_iff (infinityPlace K)
      (fun x => -log (RatFunc.inftyValuation K x))
    · intro x y hx hy
      rw [map_mul, log_mul ((Valuation.ne_zero_iff _).mpr hx) ((Valuation.ne_zero_iff _).mpr hy)]
      exact neg_add _ _
    · refine ⟨(RatFunc.X : RatFunc K)⁻¹, inv_ne_zero RatFunc.X_ne_zero, ?_⟩
      rw [map_inv₀, RatFunc.inftyValuation.X, ← exp_neg, log_exp]
      norm_num
    · intro x hx
      change 0 ≤ -log (RatFunc.inftyValuation K x) ↔ RatFunc.inftyValuation K x ≤ 1
      rw [← WithZero.log_le_log ((Valuation.ne_zero_iff _).mpr hx) one_ne_zero, log_one]
      omega
    · exact hf
  rw [← hnorm, RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero K hf, log_exp]

theorem infinityPlace_ord_X : (infinityPlace K).ord (RatFunc.X : RatFunc K) = -1 := by
  rw [infinityPlace_ord K RatFunc.X_ne_zero, RatFunc.intDegree_X]

end
end Dubon2026.SourceCurve.RationalFunction
