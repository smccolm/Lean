import Dubon2026.SourceOriginalJFiberDegree

/-! DUB-17/18 -> numerical modular genus -> degree sums at finite fibers
and infinity. The original j-field degree supplies the total pole order
as well as every finite fiber's multiplicity. Finite-set versions match
the canonical-divisor summation used by the genus calculation. Actual
ramification orders and elliptic/cusp cardinalities remain to be proved.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve IntermediateField
open scoped IntermediateField

variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]

theorem sum_original_j_pole_orders_eq_psi :
    (∑ᶠ v : {v : Place L (modularFunctionFieldOver N L) // v.ord (jOver N L) < 0},
      -v.1.ord (jOver N L)) = (SourceLevelProjective.dedekindPsi N : ℤ) := by
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  have ht : Transcendental L (jOver N L)⁻¹ :=
    fun h => transcendental_jOver N L (IsAlgebraic.inv_iff.mp h)
  haveI := finiteDimensional_original_over_transcendental N L ht
  have h := sum_positive_orders_eq_finrank_adjoin _ ht
  have hr : ∀ v : Place L (modularFunctionFieldOver N L), Module.finrank L v.ResidueField = 1 :=
    fun v => Module.finrank_of_bijective_algebraMap (original_place_residue_algebraMap_bijective N L v)
  simp only [hr, Nat.cast_one, mul_one] at h
  rw [adjoin_singleton_inv_eq, finrank_original_over_j_eq_psi] at h
  let e : {v : Place L (modularFunctionFieldOver N L) // 0 < v.ord (jOver N L)⁻¹} ≃
      {v : Place L (modularFunctionFieldOver N L) // v.ord (jOver N L) < 0} :=
    Equiv.subtypeEquivRight fun v => by rw [v.ord_inv, neg_pos]
  rw [← finsum_comp_equiv e]
  change (∑ᶠ v : {v : Place L (modularFunctionFieldOver N L) // 0 < v.ord (jOver N L)⁻¹},
    -v.1.ord (jOver N L)) = _
  simpa only [Place.ord_inv] using h

theorem sum_original_j_fiber_orders_finset (c : L)
    (S : Finset (Place L (modularFunctionFieldOver N L)))
    (hS : ∀ v, v ∈ S ↔ 0 < v.ord (jOver N L - algebraMap L (modularFunctionFieldOver N L) c)) :
    (∑ v ∈ S, v.ord (jOver N L - algebraMap L (modularFunctionFieldOver N L) c)) =
      (SourceLevelProjective.dedekindPsi N : ℤ) := by
  have h := sum_original_j_fiber_orders_eq_psi N L c
  have he : {v : Place L (modularFunctionFieldOver N L) |
      0 < v.ord (jOver N L - algebraMap L (modularFunctionFieldOver N L) c)} = (S : Set _) :=
    Set.ext fun v => (hS v).symm
  have h' := (finsum_set_coe_eq_finsum_mem (f := fun v : Place L (modularFunctionFieldOver N L) =>
    v.ord (jOver N L - algebraMap L (modularFunctionFieldOver N L) c))
    {v | 0 < v.ord (jOver N L - algebraMap L (modularFunctionFieldOver N L) c)}).symm.trans h
  rw [he, finsum_mem_coe_finset] at h'
  exact h'

theorem sum_original_j_pole_orders_finset
    (S : Finset (Place L (modularFunctionFieldOver N L)))
    (hS : ∀ v, v ∈ S ↔ v.ord (jOver N L) < 0) :
    (∑ v ∈ S, -v.ord (jOver N L)) = (SourceLevelProjective.dedekindPsi N : ℤ) := by
  have h := sum_original_j_pole_orders_eq_psi N L
  have he : {v : Place L (modularFunctionFieldOver N L) | v.ord (jOver N L) < 0} = (S : Set _) :=
    Set.ext fun v => (hS v).symm
  have h' := (finsum_set_coe_eq_finsum_mem (f := fun v : Place L (modularFunctionFieldOver N L) =>
    -v.ord (jOver N L)) {v | v.ord (jOver N L) < 0}).symm.trans h
  rw [he, finsum_mem_coe_finset] at h'
  exact h'

end
end Dubon2026.SourceFunctionField
