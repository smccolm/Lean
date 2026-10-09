import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Algebra.Group.Subgroup.Lattice

/-! # Genuine finite topological generators pass through original continuous surjections -/

namespace Dubon2026

noncomputable section

variable {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H] [DecidableEq H]

/-- The actual images of original topological generators topologically generate every original continuous quotient. -/
theorem continuous_surjective_image_topological_generators
    (f : G →* H) (hf : Continuous f) (hsurj : Function.Surjective f)
    (S : Finset G) (hS : (Subgroup.closure (S : Set G)).topologicalClosure = ⊤) :
    (Subgroup.closure ((S.image f) : Set H)).topologicalClosure = ⊤ := by
  classical
  let J := (Subgroup.closure ((S.image f) : Set H)).topologicalClosure
  have hclosed : IsClosed (J.comap f : Set G) :=
    (Subgroup.isClosed_topologicalClosure _).preimage hf
  have hgen : Subgroup.closure (S : Set G) ≤ J.comap f := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    apply Subgroup.le_topologicalClosure
    apply Subgroup.subset_closure
    exact Finset.mem_image.mpr ⟨g, hg, rfl⟩
  have hall := Subgroup.topologicalClosure_minimal _ hgen hclosed
  rw [hS] at hall
  apply eq_top_iff.mpr
  intro y _
  obtain ⟨g, rfl⟩ := hsurj y
  exact hall (Subgroup.mem_top g)

end
end Dubon2026
