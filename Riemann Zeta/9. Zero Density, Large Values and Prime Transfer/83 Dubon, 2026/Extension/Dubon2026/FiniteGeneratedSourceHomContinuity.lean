import Dubon2026.FiniteSourceHomActionContinuity
import Mathlib.RingTheory.Finiteness.Basic

/-! # Continuous Hom action for the actual finite relation lattices

Evaluation on a finite generating set suffices for continuity. This is
needed for the finite free cover and relation lattice pulled back to the
original arithmetic Galois group in DUB-17's cup/connecting comparison;
those integer lattices have infinitely many elements.
-/
namespace Dubon2026
noncomputable section
variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A B : Rep.{0} R G) [Module.Finite R A]
  [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace B] [DiscreteTopology B]
  [TopologicalSpace ((CategoryTheory.ihom A).obj B)]
  [DiscreteTopology ((CategoryTheory.ihom A).obj B)]

/-- The conjugate Hom action is continuous when its original source
is finitely generated and both original coefficient actions are continuous. -/
theorem finiteGeneratedSourceHomAction_continuous
    (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
    (hB : Continuous (fun z : G × B => B.ρ z.1 z.2)) :
    Continuous (fun z : G × (CategoryTheory.ihom A).obj B =>
      ((CategoryTheory.ihom A).obj B).ρ z.1 z.2) := by
  classical
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule R A).FG)
  have hemb : Topology.IsEmbedding
      (fun f : (CategoryTheory.ihom A).obj B =>
        fun x : s => (show A →ₗ[R] B from f) x.val) :=
    (Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
      continuous_of_discreteTopology (by
        intro f g h
        apply LinearMap.ext_on hs
        intro x hx
        exact congrFun h ⟨x, hx⟩)
      (fun _ _ => isOpen_discrete _)).isEmbedding
  apply hemb.continuous_iff.mpr
  apply continuous_pi
  intro x
  change Continuous (fun z : G × (CategoryTheory.ihom A).obj B =>
    B.ρ z.1 ((show A →ₗ[R] B from z.2) (A.ρ z.1⁻¹ x.val)))
  have he : Continuous (fun z : (CategoryTheory.ihom A).obj B × A =>
      (show A →ₗ[R] B from z.1) z.2) := continuous_of_discreteTopology
  exact hB.comp (continuous_fst.prodMk (he.comp (continuous_snd.prodMk
    (hA.comp (continuous_fst.inv.prodMk continuous_const)))))

end
end Dubon2026
