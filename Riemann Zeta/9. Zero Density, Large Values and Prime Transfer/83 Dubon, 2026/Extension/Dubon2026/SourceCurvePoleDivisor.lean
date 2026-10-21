import Dubon2026.SourceCurveRiemannRochSpace
import Dubon2026.SourceCurveTranscendentalDegree

/-! DUB-17/18 -> function-field Riemann--Roch -> bounded global index.
The actual pole divisor of a coordinate has degree equal to the degree of
the field over that coordinate. This directly reuses the proved positive
order identity, avoiding a separate classification of rational-function
places and their prolongations for the pole-divisor construction.
-/
namespace Dubon2026.SourceCurve
noncomputable section
open IntermediateField
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The actual finite pole divisor of a function with finite place-order support. -/
def poleDivisor (f : F) (hf : {v : Place K F | v.ord f ≠ 0}.Finite) : Divisor K F :=
  Finsupp.ofSupportFinite (fun v => max (-v.ord f) 0) (hf.subset (by
    intro v hv h
    apply hv
    simp [h]))

theorem poleDivisor_apply (f : F) (hf : {v : Place K F | v.ord f ≠ 0}.Finite)
    (v : Place K F) : poleDivisor f hf v = max (-v.ord f) 0 := rfl

theorem poleDivisor_nonneg (f : F) (hf : {v : Place K F | v.ord f ≠ 0}.Finite) :
    0 ≤ poleDivisor f hf := fun _ => le_max_right _ _

theorem mem_lSpace_poleDivisor (f : F) (hf : {v : Place K F | v.ord f ≠ 0}.Finite) :
    f ∈ LSpace (poleDivisor f hf) := by
  apply mem_lSpace_iff_ord.mpr
  right
  intro v
  rw [poleDivisor_apply]
  have := le_max_left (-v.ord f) 0
  omega

theorem degree_poleDivisor_eq_positive_inverse (f : F)
    (hf : {v : Place K F | v.ord f ≠ 0}.Finite) :
    Divisor.degree (poleDivisor f hf) =
      ∑ᶠ v : {v : Place K F // 0 < v.ord f⁻¹},
        v.1.ord f⁻¹ * (Module.finrank K v.1.ResidueField : ℤ) := by
  classical
  rw [Divisor.degree_eq_finsum]
  have he := finsum_set_coe_eq_finsum_mem (f := fun v : Place K F =>
    v.ord f⁻¹ * (Module.finrank K v.ResidueField : ℤ)) {v | 0 < v.ord f⁻¹}
  rw [finsum_mem_def] at he
  refine Eq.trans ?_ he.symm
  apply finsum_congr
  intro v
  simp only [poleDivisor_apply, Set.indicator_apply, Set.mem_setOf_eq, v.ord_inv]
  by_cases h : 0 < -v.ord f
  · rw [if_pos h, max_eq_left (le_of_lt h)]
  · rw [if_neg h, max_eq_right (le_of_not_gt h), zero_mul]

theorem degree_poleDivisor_eq_finrank [CharZero K] (t : F) (ht : Transcendental K t)
    [FiniteDimensional K⟮t⟯ F] (hf : {v : Place K F | v.ord t ≠ 0}.Finite) :
    Divisor.degree (poleDivisor t hf) = (Module.finrank K⟮t⟯ F : ℤ) := by
  have hti : Transcendental K t⁻¹ := fun hi => ht (IsAlgebraic.inv_iff.mp hi)
  haveI : FiniteDimensional K⟮t⁻¹⟯ F := by
    rw [adjoin_singleton_inv_eq]
    infer_instance
  rw [degree_poleDivisor_eq_positive_inverse,
    sum_positive_orders_eq_finrank_adjoin t⁻¹ hti, adjoin_singleton_inv_eq]

end
end Dubon2026.SourceCurve
