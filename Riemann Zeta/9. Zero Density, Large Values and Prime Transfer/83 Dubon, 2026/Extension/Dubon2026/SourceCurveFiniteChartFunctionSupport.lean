import Dubon2026.SourceCurvePlaceCenters

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> principal
divisors on the residue curve. Dedekind-chart factorization already bounds
positive support for integral elements. Clearing a denominator gives finite
support for every actual rational function on that chart, in any characteristic. -/
namespace Dubon2026.SourceCurve
noncomputable section

theorem finite_chart_function_support
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
    (f : F) : {v : Place K F | (∀ r : R, algebraMap R F r ∈ v.toValuationSubring) ∧
      v.ord f ≠ 0}.Finite := by
  classical
  by_cases hf : f = 0
  · subst f
    simp only [Place.ord_zero, ne_eq, not_true_eq_false, and_false, Set.setOf_false]
    exact Set.finite_empty
  obtain ⟨a, b, hb, he⟩ := IsFractionRing.div_surjective (A := R) f
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbF : algebraMap R F b ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R F).ne_iff.mpr hb0
  have haF : algebraMap R F a ≠ 0 := by
    intro h
    exact hf (by rw [← he, h, zero_div])
  have ha0 : a ≠ 0 := fun h => haF (by rw [h, map_zero])
  refine ((Place.finite_setOf_forall_mem_and_ord_pos (K := K) (F := F) ha0).union
    (Place.finite_setOf_forall_mem_and_ord_pos (K := K) (F := F) hb0)).subset ?_
  rintro v ⟨hv, hne⟩
  have ha := v.ord_nonneg_of_mem (hv a)
  have hb' := v.ord_nonneg_of_mem (hv b)
  have hord : v.ord f = v.ord (algebraMap R F a) - v.ord (algebraMap R F b) := by
    rw [← he, div_eq_mul_inv, v.ord_mul haF (inv_ne_zero hbF), v.ord_inv, sub_eq_add_neg]
  change ((∀ r : R, algebraMap R F r ∈ v.toValuationSubring) ∧
    0 < v.ord (algebraMap R F a)) ∨ ((∀ r : R, algebraMap R F r ∈ v.toValuationSubring) ∧
    0 < v.ord (algebraMap R F b))
  by_cases ha' : 0 < v.ord (algebraMap R F a)
  · exact Or.inl ⟨hv, ha'⟩
  · exact Or.inr ⟨hv, by omega⟩

end
end Dubon2026.SourceCurve
