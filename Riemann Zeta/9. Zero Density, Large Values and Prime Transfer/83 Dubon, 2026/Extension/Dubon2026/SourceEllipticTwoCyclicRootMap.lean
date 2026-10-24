import Dubon2026.SourceIntegralTwoCyclicRoots
import Dubon2026.SourceEllipticOddCyclicRootMap

/-! The actual degree-two cyclic-subgroup-to-root map. Its generator is the
unique nonzero point of that subgroup, and the already proved degree-two
product gives surjectivity. This is the remaining branch of the prime map. -/

namespace Dubon2026.SourceFunctionField.IntegralJCoordinate
open Polynomial WeierstrassCurve SourceEllipticVelu
noncomputable section
variable {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve K)

/-- An order-two subgroup has only one generator in the actual point group. -/
theorem point_eq_of_order_two_zmultiples_eq {P Q : W.toAffine.Point}
    (hP : addOrderOf P = 2) (hQ : addOrderOf Q = 2)
    (hPQ : AddSubgroup.zmultiples P = AddSubgroup.zmultiples Q) : P = Q := by
  have hf : IsOfFinAddOrder P := addOrderOf_pos_iff.mp (by omega)
  have hmem : Q ∈ AddSubgroup.zmultiples P := by
    rw [hPQ]
    exact AddSubgroup.mem_zmultiples Q
  rw [hf.mem_zmultiples_iff_mem_range_addOrderOf, hP] at hmem
  simp only [Finset.mem_image, Finset.mem_range] at hmem
  obtain ⟨n, hn, he⟩ := hmem
  interval_cases n
  · simp only [zero_nsmul] at he
    have hQ0 : addOrderOf (0 : W.toAffine.Point) = 2 := he.symm ▸ hQ
    simp only [addOrderOf_zero] at hQ0
    omega
  · simpa only [one_nsmul] using he

variable [W.IsElliptic] [IsAlgClosed K]

/-- The literal degree-two quotient gives the actual cyclic-subgroup root map. -/
def twoCyclicRootMap (h2 : (2 : K) ≠ 0) :
    {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = 2} →
      {x : K // (relationAtSeed (modularPolynomial 2) W.j).IsRoot x} := fun H =>
  ⟨twoQuotientJ W (primeKernelGenerator_order W 2 H),
    modularPolynomial_isRoot_twoQuotientJ W h2 _ (primeKernelGenerator_order W 2 H)⟩

/-- The map agrees with the quotient of the actual nonzero order-two point in its subgroup. -/
theorem twoCyclicRootMap_eq_quotient (h2 : (2 : K) ≠ 0)
    (H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = 2})
    {P : W.toAffine.Point} (hP : addOrderOf P = 2)
    (hPH : AddSubgroup.zmultiples P = H.1) :
    (twoCyclicRootMap W h2 H).1 = twoQuotientJ W hP := by
  have he := point_eq_of_order_two_zmultiples_eq W (primeKernelGenerator_order W 2 H) hP
    ((primeKernelGenerator_zmultiples W 2 H).trans hPH.symm)
  simp only [twoCyclicRootMap, he]

/-- Every root of the actual degree-two modular polynomial arises from an original cyclic subgroup. -/
theorem twoCyclicRootMap_surjective (h2 : (2 : K) ≠ 0) :
    Function.Surjective (twoCyclicRootMap W h2) := by
  intro x
  obtain ⟨P, hP, hx⟩ := (modularPolynomial_isRoot_iff_exists_twoQuotientJ W h2 x.1).mp x.2
  let H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = 2} :=
    ⟨AddSubgroup.zmultiples P,
      (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top _).mpr ⟨P, rfl⟩,
      (Nat.card_zmultiples P).trans hP⟩
  refine ⟨H, Subtype.ext ?_⟩
  exact (twoCyclicRootMap_eq_quotient W h2 H hP rfl).trans hx

end
end Dubon2026.SourceFunctionField.IntegralJCoordinate
