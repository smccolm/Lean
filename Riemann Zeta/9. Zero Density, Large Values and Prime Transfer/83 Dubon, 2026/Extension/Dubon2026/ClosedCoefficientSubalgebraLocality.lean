import Dubon2026.LocalCoefficientReduction
import Mathlib.Topology.Algebra.Algebra
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Ring

/-! # Units and locality in a closed original coefficient subalgebra -/

namespace Dubon2026
noncomputable section
open Filter Topology

variable {O R : Type*} [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R] [WithIdeal R]

/-- A closed original coefficient subalgebra reflects actual units when the ambient maximal-adic coefficient ring has the original residue field. -/
theorem closedCoefficientSubalgebra_isUnit
    (hR : (WithIdeal.i : Ideal R) = IsLocalRing.maximalIdeal R)
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (S : Subalgebra O R) (hS : IsClosed (S : Set R)) (x : S)
    (hx : IsUnit (x : R)) : IsUnit x := by
  obtain ⟨u, hu⟩ := hx
  obtain ⟨o, ho⟩ := IsLocalRing.residue_surjective
    (localCoefficientReduction eR (↑u⁻¹ : R))
  let a : R := algebraMap O R o
  let t : R := 1 - a * (u : R)
  have ha : localCoefficientReduction eR a = localCoefficientReduction eR (↑u⁻¹ : R) := by
    exact ((localCoefficientReduction eR).commutes o).trans ho
  have htzero : localCoefficientReduction eR t = 0 := by
    change localCoefficientReduction eR (1 - a * (u : R)) = 0
    rw [map_sub, map_one, map_mul, ha, ← map_mul, Units.inv_mul, map_one, sub_self]
  have ht : IsTopologicallyNilpotent t :=
    WithIdeal.isTopologicallyNilpotent_of_mem (hR ▸
      (localCoefficientReduction_eq_zero_iff eR t).mp htzero)
  have huS : (u : R) ∈ S := hu.symm ▸ x.property
  have haS : a ∈ S := S.algebraMap_mem o
  have htS : t ∈ S := S.sub_mem S.one_mem (S.mul_mem haS huS)
  let z : ℕ → R := fun n => (∑ i ∈ Finset.range n, t ^ i) * a
  have hzS (n : ℕ) : z n ∈ S :=
    S.mul_mem (S.sum_mem fun i _ => S.pow_mem htS i) haS
  have hzu (n : ℕ) : z n * (u : R) = 1 - t ^ n := by
    change ((∑ i ∈ Finset.range n, t ^ i) * a) * (u : R) = _
    rw [mul_assoc]
    have hat : a * (u : R) = 1 - t := by dsimp [t]; ring
    rw [hat, geom_sum_mul_neg]
  have hz (n : ℕ) : z n = (1 - t ^ n) * (↑u⁻¹ : R) := by
    rw [← hzu, mul_assoc, Units.mul_inv, mul_one]
  have hzlim : Tendsto z atTop (𝓝 (↑u⁻¹ : R)) := by
    rw [show z = (fun n => (1 - t ^ n) * (↑u⁻¹ : R)) from funext hz]
    have hc : Tendsto (fun _ : ℕ => (1 : R)) atTop (𝓝 (1 : R)) := tendsto_const_nhds
    simpa only [sub_zero, one_mul] using
      (hc.sub ht).mul_const (↑u⁻¹ : R)
  have hinv : (↑u⁻¹ : R) ∈ S := hS.mem_of_tendsto hzlim (Filter.Eventually.of_forall hzS)
  refine ⟨⟨x, ⟨↑u⁻¹, hinv⟩, ?_, ?_⟩, rfl⟩
  · apply Subtype.ext
    change (x : R) * (↑u⁻¹ : R) = 1
    rw [← hu, Units.mul_inv]
  · apply Subtype.ext
    change (↑u⁻¹ : R) * (x : R) = 1
    rw [← hu, Units.inv_mul]

/-- The actual inclusion of the closed original coefficient subalgebra reflects units. -/
theorem closedCoefficientSubalgebra_isLocalHom
    (hR : (WithIdeal.i : Ideal R) = IsLocalRing.maximalIdeal R)
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (S : Subalgebra O R) (hS : IsClosed (S : Set R)) :
    IsLocalHom S.val.toRingHom :=
  ⟨fun x hx => closedCoefficientSubalgebra_isUnit hR eR S hS x hx⟩

/-- The closed original coefficient subalgebra is itself local, for its existing ring operations. -/
theorem closedCoefficientSubalgebra_isLocalRing
    (hR : (WithIdeal.i : Ideal R) = IsLocalRing.maximalIdeal R)
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (S : Subalgebra O R) (hS : IsClosed (S : Set R)) : IsLocalRing S := by
  letI := closedCoefficientSubalgebra_isLocalHom hR eR S hS
  exact S.val.toRingHom.domain_isLocalRing

end
end Dubon2026
