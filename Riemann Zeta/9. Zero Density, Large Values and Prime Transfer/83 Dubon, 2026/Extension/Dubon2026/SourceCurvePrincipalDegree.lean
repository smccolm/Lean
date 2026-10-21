import Dubon2026.SourceCurveTranscendentalDegree
import Dubon2026.SourceCurveTranscendence

/-! DUB-17/18 -> regular differential dimension -> principal divisors.
The literal sum of normalized place orders, weighted by residue degrees,
vanishes: positive and negative orders have the same degree, because a
transcendental coordinate and its inverse generate the same subfield.
-/
namespace Dubon2026.SourceCurve
noncomputable section
open IntermediateField

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem sum_orders_eq_positive_sub_inverse (f : F)
    (hf : {v : Place K F | v.ord f ≠ 0}.Finite) :
    (∑ᶠ v : Place K F, v.ord f * (Module.finrank K v.ResidueField : ℤ)) =
      (∑ᶠ v : {v : Place K F // 0 < v.ord f},
        v.1.ord f * (Module.finrank K v.1.ResidueField : ℤ)) -
      (∑ᶠ v : {v : Place K F // 0 < v.ord f⁻¹},
        v.1.ord f⁻¹ * (Module.finrank K v.1.ResidueField : ℤ)) := by
  classical
  let p : Place K F → ℤ := fun v =>
    if 0 < v.ord f then v.ord f * (Module.finrank K v.ResidueField : ℤ) else 0
  let n : Place K F → ℤ := fun v =>
    if 0 < v.ord f⁻¹ then v.ord f⁻¹ * (Module.finrank K v.ResidueField : ℤ) else 0
  have hp : p.HasFiniteSupport := hf.subset (by
    intro v hv
    simp only [Function.mem_support, p] at hv
    change v.ord f ≠ 0
    intro h
    simp [h] at hv)
  have hn : n.HasFiniteSupport := hf.subset (by
    intro v hv
    simp only [Function.mem_support, n, v.ord_inv] at hv
    change v.ord f ≠ 0
    intro h
    simp [h] at hv)
  have he : ∀ v : Place K F,
      v.ord f * (Module.finrank K v.ResidueField : ℤ) = p v - n v := by
    intro v
    simp only [p, n, v.ord_inv]
    split_ifs with hpos hneg hneg
    · omega
    · ring
    · ring
    · have hz : v.ord f = 0 := by omega
      simp [hz]
  rw [finsum_congr he, finsum_sub_distrib hp hn]
  congr 1
  · have h := finsum_set_coe_eq_finsum_mem (f := fun v : Place K F =>
      v.ord f * (Module.finrank K v.ResidueField : ℤ)) {v | 0 < v.ord f}
    rw [finsum_mem_def] at h
    simpa only [Set.indicator_apply, Set.mem_setOf_eq, p] using h.symm
  · have h := finsum_set_coe_eq_finsum_mem (f := fun v : Place K F =>
      v.ord f⁻¹ * (Module.finrank K v.ResidueField : ℤ)) {v | 0 < v.ord f⁻¹}
    rw [finsum_mem_def] at h
    simpa only [Set.indicator_apply, Set.mem_setOf_eq, n] using h.symm

theorem sum_orders_eq_zero_of_finite_coordinates [CharZero K]
    (hfinite : ∀ t : F, Transcendental K t → FiniteDimensional K⟮t⟯ F)
    (f : F) (hf : {v : Place K F | v.ord f ≠ 0}.Finite) :
    (∑ᶠ v : Place K F, v.ord f * (Module.finrank K v.ResidueField : ℤ)) = 0 := by
  classical
  by_cases ht : Transcendental K f
  · have hti : Transcendental K f⁻¹ := fun hi => ht (IsAlgebraic.inv_iff.mp hi)
    haveI : FiniteDimensional K⟮f⟯ F := hfinite f ht
    haveI : FiniteDimensional K⟮f⁻¹⟯ F := hfinite f⁻¹ hti
    rw [sum_orders_eq_positive_sub_inverse f hf,
      sum_positive_orders_eq_finrank_adjoin f ht,
      sum_positive_orders_eq_finrank_adjoin f⁻¹ hti,
      adjoin_singleton_inv_eq, sub_self]
  · have ha : IsAlgebraic K f := not_not.mp ht
    simp only [Place.ord_eq_zero_of_isAlgebraic _ ha, zero_mul, finsum_zero]

end
end Dubon2026.SourceCurve
