import Dubon2026.SourceRatFuncSpecializationOrder

/-! DUB-17/18 -> reverse genus -> exceptional place fibers.
The existing degree-one sum for a rational generator proves uniqueness
of its positive place. This avoids a separate classification of rational
valuation rings and supplies the base-place comparison for Galois lifting. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open IntermediateField
variable {K : Type*} [Field K] [IsAlgClosed K]

theorem rational_finite_value_place_unique (a : K) (v w : Place K (RatFunc K))
    (hv : 0 < v.ord (RatFunc.X - algebraMap K (RatFunc K) a))
    (hw : 0 < w.ord (RatFunc.X - algebraMap K (RatFunc K) a)) : v = w := by
  classical
  let t : RatFunc K := RatFunc.X - algebraMap K (RatFunc K) a
  have ht : Transcendental K t := by
    intro h
    apply RatFunc.transcendental_X (K := K)
    simpa only [t, sub_add_cancel] using h.add (isAlgebraic_algebraMap a)
  have hgen : K⟮t⟯ = ⊤ := by
    apply top_unique
    rw [← RatFunc.adjoin_X]
    apply adjoin_simple_le_iff.mpr
    have h := add_mem (mem_adjoin_simple_self K t) (IntermediateField.algebraMap_mem K⟮t⟯ a)
    simpa only [t, sub_add_cancel] using h
  obtain ⟨hfinite, hsep⟩ := finite_separable_of_adjoin_eq_top t hgen
  have hS : {u : Place K (RatFunc K) | 0 < u.ord t}.Finite :=
    (finite_function_support_of_separating_coordinate t ht t).subset fun _ hu => ne_of_gt hu
  letI : Fintype {u : Place K (RatFunc K) // 0 < u.ord t} := hS.fintype
  have hs := sum_positive_orders_generator t ht hgen
  rw [finsum_eq_sum_of_fintype] at hs
  have horder (u : {u : Place K (RatFunc K) // 0 < u.ord t}) : u.val.ord t = 1 :=
    rational_finite_value_order_eq_one u.val a u.property
  simp only [horder, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hs
  have hc : Fintype.card {u : Place K (RatFunc K) // 0 < u.ord t} ≤ 1 := by
    exact_mod_cast le_of_eq hs
  haveI := Fintype.card_le_one_iff_subsingleton.mp hc
  exact congrArg Subtype.val (Subsingleton.elim
    (⟨v, hv⟩ : {u : Place K (RatFunc K) // 0 < u.ord t}) ⟨w, hw⟩)

end
end Dubon2026.SourceCurve.Place
