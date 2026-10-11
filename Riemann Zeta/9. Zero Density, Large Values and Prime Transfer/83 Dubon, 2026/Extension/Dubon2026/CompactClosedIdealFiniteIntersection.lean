import Mathlib.Topology.Compactness.Compact
import Mathlib.RingTheory.Ideal.Lattice

/-! # Finite original closed-ideal intersections inside an original open ideal -/

namespace Dubon2026

variable {A ι : Type*} [CommRing A] [TopologicalSpace A] [CompactSpace A]

/-- Compactness supplies a finite original ideal intersection inside any original open ideal containing the full intersection. A specified original index is retained, so the finite family is nonempty in model-closure applications. -/
theorem compactClosedIdeals_finiteIntersection_le
    (I : ι → Ideal A) (hI : ∀ i, IsClosed (I i : Set A))
    (U : Ideal A) (hU : IsOpen (U : Set A)) (hsub : (⨅ i, I i) ≤ U) (i₀ : ι) :
    ∃ s : Finset ι, i₀ ∈ s ∧ (⨅ i ∈ s, I i) ≤ U := by
  classical
  have hz : ((U : Set A)ᶜ ∩ ⋂ i, (I i : Set A)) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hx.1 (hsub (Ideal.mem_iInf.mpr (Set.mem_iInter.mp hx.2)))
  obtain ⟨s, hs⟩ := hU.isClosed_compl.isCompact.elim_finite_subfamily_closed
    (fun i => (I i : Set A)) hI hz
  refine ⟨insert i₀ s, Finset.mem_insert_self _ _, ?_⟩
  intro x hx
  by_contra hnx
  have hmem : x ∈ ⋂ i ∈ s, (I i : Set A) := by
    apply Set.mem_iInter.mpr
    intro i
    apply Set.mem_iInter.mpr
    intro hi
    exact Ideal.mem_iInf.mp (Ideal.mem_iInf.mp hx i) (Finset.mem_insert_of_mem hi)
  have hempty : x ∈ (∅ : Set A) := hs ▸ ⟨hnx, hmem⟩
  exact hempty

end Dubon2026
