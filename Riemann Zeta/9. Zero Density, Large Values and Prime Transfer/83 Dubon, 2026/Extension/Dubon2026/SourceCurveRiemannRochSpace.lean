import Dubon2026.SourceCurveDivisors
import Dubon2026.SourceCurveOrders

/-! DUB-17/18 -> the matching cusp-form lower bound -> regular differential
dimension -> the canonical-divisor Riemann--Roch space. These are the literal
valuation bounds of Def_AlgebraicCurve_Repartitions and
Def_AlgebraicCurve_AdelicIndex, anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2. No Riemann--Roch theorem
is assumed or claimed here.
-/
namespace Dubon2026.SourceCurve
noncomputable section
open WithZero

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place
variable (v : Place K F)

theorem adicValuation_le_one_of_mem {x : F} (hx : x ∈ v.toValuationSubring) :
    v.adicValuation x ≤ 1 := by
  have h := (v.adicValuation_coe ⟨x, hx⟩).trans_le
    (v.heightOneSpectrum.intValuation_le_one ⟨x, hx⟩)
  simpa using h

theorem adicValuation_algebraMap_le_one (a : K) :
    v.adicValuation (algebraMap K F a) ≤ 1 :=
  v.adicValuation_le_one_of_mem (v.algebraMap_mem' a)

end Place

/-- Functions whose pole divisor is bounded by the given actual divisor. -/
def LSpace (D : Divisor K F) : Submodule K F where
  carrier := {f | ∀ v : Place K F, v.adicValuation f ≤ exp (D v)}
  zero_mem' := by
    intro v
    simp
  add_mem' := by
    intro f g hf hg v
    exact (Valuation.map_add _ _ _).trans (max_le (hf v) (hg v))
  smul_mem' := by
    intro c f hf v
    show v.adicValuation (c • f) ≤ exp (D v)
    rw [Algebra.smul_def, map_mul]
    exact (mul_le_of_le_one_left' (v.adicValuation_algebraMap_le_one c)).trans (hf v)

theorem mem_lSpace_iff_ord {D : Divisor K F} {f : F} :
    f ∈ LSpace D ↔ f = 0 ∨ ∀ v : Place K F, -D v ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · exact ⟨fun _ => Or.inl rfl, fun _ => (LSpace D).zero_mem⟩
  · refine Iff.trans ?_ (or_iff_right hf).symm
    refine forall_congr' fun v => ?_
    have hne : v.adicValuation f ≠ 0 := v.adicValuation_ne_zero hf
    rw [show v.adicValuation f = exp (-v.ord f) by
          rw [Place.ord, neg_neg, exp_log hne],
      exp_le_exp, neg_le]

theorem lSpace_mono {D E : Divisor K F} (hDE : D ≤ E) : LSpace D ≤ LSpace E :=
  fun _ hf v => (hf v).trans (exp_le_exp.mpr (hDE v))

theorem algebraMap_mem_lSpace_zero (c : K) :
    algebraMap K F c ∈ LSpace (0 : Divisor K F) := fun v => by
  rw [Finsupp.coe_zero, Pi.zero_apply, exp_zero]
  exact v.adicValuation_algebraMap_le_one c

end
end Dubon2026.SourceCurve
