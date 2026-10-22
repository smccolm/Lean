import Dubon2026.SourceOriginalPrincipalDivisors
import Dubon2026.SourceCurveDivisorDegree
import Dubon2026.SourceOriginalPlaceEvaluation

/-! DUB-17/18 -> original torsion cardinality -> compact complex curve.
The actual principal divisor has finite support and degree zero. Subtracting
a constant preserves its pole orders, so all nonconstant fibers have the
same total positive order. This is the global bound that will exhaust the
nearby analytic preimages. No divisor existence or degree premise is supplied.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable (N : ℕ) [NeZero N]

omit [NeZero N] in
theorem original_sub_const_mem_iff (v : Place ℂ (modularFunctionFieldOver N ℂ))
    (f : modularFunctionFieldOver N ℂ) (a : ℂ) :
    f - algebraMap ℂ (modularFunctionFieldOver N ℂ) a ∈ v.toValuationSubring ↔
      f ∈ v.toValuationSubring := by
  constructor
  · intro h
    simpa only [sub_add_cancel] using add_mem h (v.algebraMap_mem' a)
  · exact fun h => sub_mem h (v.algebraMap_mem' a)

omit [NeZero N] in
theorem original_ord_sub_const_of_pole (v : Place ℂ (modularFunctionFieldOver N ℂ))
    {f : modularFunctionFieldOver N ℂ} (hf : f ∉ v.toValuationSubring) (a : ℂ) :
    v.ord (f - algebraMap ℂ (modularFunctionFieldOver N ℂ) a) = v.ord f := by
  by_cases ha : a = 0
  · simp only [ha, map_zero, sub_zero]
  have hf0 : f ≠ 0 := fun h => hf (h ▸ zero_mem _)
  have ha0 : -(algebraMap ℂ (modularFunctionFieldOver N ℂ) a) ≠ 0 :=
    neg_ne_zero.mpr (by simpa only [map_zero] using
      (algebraMap ℂ (modularFunctionFieldOver N ℂ)).injective.ne ha)
  have ho : v.ord f < 0 := lt_of_not_ge (fun h => hf (v.mem_of_ord_nonneg h))
  rw [sub_eq_add_neg]
  apply v.ord_add_eq_of_lt hf0 ha0
  rwa [v.ord_neg, v.ord_algebraMap]

theorem original_divisor_sum_support (D : Divisor ℂ (modularFunctionFieldOver N ℂ)) :
    (∑ v ∈ D.support, D v) = Divisor.degree D := by
  have hr : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), Module.finrank ℂ v.ResidueField = 1 :=
    fun v => Module.finrank_of_bijective_algebraMap
      (original_place_residue_algebraMap_bijective N ℂ v)
  simp only [Divisor.degree_eq_sum_support, hr, Nat.cast_one, mul_one]

end
end Dubon2026.SourceFunctionField
