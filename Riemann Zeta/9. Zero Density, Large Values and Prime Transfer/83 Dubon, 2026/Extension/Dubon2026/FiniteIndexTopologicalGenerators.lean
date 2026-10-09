import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Subgroup.Lattice

/-! # Genuine finite topological generators extend across an original finite-index normal subgroup -/

namespace Dubon2026

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Original finite coset representatives together with genuine topological generators of the original normal subgroup topologically generate the entire original group. -/
theorem finiteIndex_normal_topological_generators
    (K : Subgroup G) [K.Normal] [Finite (G ⧸ K)]
    (S : Finset K) (hS : (Subgroup.closure (S : Set K)).topologicalClosure = ⊤) :
    ∃ T : Finset G, (Subgroup.closure (T : Set G)).topologicalClosure = ⊤ := by
  classical
  letI : Fintype (G ⧸ K) := Fintype.ofFinite _
  choose r hr using QuotientGroup.mk'_surjective K
  let T : Finset G := S.image Subtype.val ∪ Finset.univ.image r
  let J := (Subgroup.closure (T : Set G)).topologicalClosure
  have hT : ∀ g ∈ T, g ∈ J := fun g hg =>
    Subgroup.le_topologicalClosure _ (Subgroup.subset_closure hg)
  have hclosed : IsClosed (J.comap K.subtype : Set K) :=
    (Subgroup.isClosed_topologicalClosure _).preimage continuous_subtype_val
  have hgen : Subgroup.closure (S : Set K) ≤ J.comap K.subtype := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    apply hT
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨g, hg, rfl⟩)
  have hall := Subgroup.topologicalClosure_minimal _ hgen hclosed
  rw [hS] at hall
  have hKJ : K ≤ J := fun g hg => hall (Subgroup.mem_top (⟨g, hg⟩ : K))
  have hrJ : ∀ q, r q ∈ J := fun q => hT _
    (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q, Finset.mem_univ q, rfl⟩))
  refine ⟨T, eq_top_iff.mpr ?_⟩
  intro g _
  have hgK : (r (QuotientGroup.mk' K g))⁻¹ * g ∈ K := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' K ((r (QuotientGroup.mk' K g))⁻¹ * g) = 1
    rw [map_mul, map_inv, hr, inv_mul_cancel]
  have hprod := J.mul_mem (hrJ (QuotientGroup.mk' K g)) (hKJ hgK)
  simpa only [mul_inv_cancel_left] using hprod

end
end Dubon2026
