import Dubon2026.ContinuousRepresentationRestriction

/-! # Continuity of original Hom actions with finite source coefficients

Evaluation embeds the original Hom coefficient into a finite product of
the discrete target. The original continuous source and target actions
therefore give the continuous conjugate Hom action. This is needed for the
arithmetic ES/JS/CS Hom sequence on DUB-17's global-duality route, whose
idele and class targets need not be finite.
-/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A B : Rep.{0} R G) [Finite A]
  [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace B] [DiscreteTopology B]
  [TopologicalSpace ((CategoryTheory.ihom A).obj B)]
  [DiscreteTopology ((CategoryTheory.ihom A).obj B)]

/-- Continuous original actions give the continuous conjugate Hom action for finite original source coefficients and an arbitrary discrete target. -/
theorem finiteSourceHomAction_continuous
    (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
    (hB : Continuous (fun z : G × B => B.ρ z.1 z.2)) :
    Continuous (fun z : G × (CategoryTheory.ihom A).obj B =>
      ((CategoryTheory.ihom A).obj B).ρ z.1 z.2) := by
  have hemb : Topology.IsEmbedding
      (fun f : (CategoryTheory.ihom A).obj B =>
        fun x : A => (show A →ₗ[R] B from f) x) :=
    (Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
      continuous_of_discreteTopology (by
        intro f g h
        exact LinearMap.ext (congrFun h))
      (fun _ _ => isOpen_discrete _)).isEmbedding
  apply hemb.continuous_iff.mpr
  apply continuous_pi
  intro x
  change Continuous (fun z : G × (CategoryTheory.ihom A).obj B =>
    B.ρ z.1 ((show A →ₗ[R] B from z.2) (A.ρ z.1⁻¹ x)))
  have he : Continuous (fun z : (CategoryTheory.ihom A).obj B × A =>
      (show A →ₗ[R] B from z.1) z.2) :=
    continuous_of_discreteTopology
  exact hB.comp (continuous_fst.prodMk (he.comp (continuous_snd.prodMk
    (hA.comp (continuous_fst.inv.prodMk continuous_const)))))

end
end Dubon2026
