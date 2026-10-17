import Dubon2026.FiniteGeneratedSourceHomContinuity

/-! # Continuity in the literal representation internal-Hom coordinates

The existing finite-source and finite-generator continuity results use
the categorical internal Hom. These two comparisons expose the same
proved actions in the literal representation coordinates used by the
dual relation sequence, without changing either topology or action.
-/
namespace Dubon2026
noncomputable section
variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A B : Rep.{0} R G)
  [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace B] [DiscreteTopology B]
  [TopologicalSpace ((Rep.ihom A).obj B)] [DiscreteTopology ((Rep.ihom A).obj B)]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))

include hA hB

/-- The proved finite-source action is continuous in the literal original
representation internal-Hom coordinates. -/
theorem originalInternalHomAction_continuous_of_finite [Finite A] :
    Continuous (fun z : G × (Rep.ihom A).obj B => ((Rep.ihom A).obj B).ρ z.1 z.2) := by
  letI : TopologicalSpace ((CategoryTheory.ihom A).obj B) :=
    inferInstanceAs (TopologicalSpace ((Rep.ihom A).obj B))
  letI : DiscreteTopology ((CategoryTheory.ihom A).obj B) :=
    inferInstanceAs (DiscreteTopology ((Rep.ihom A).obj B))
  exact finiteSourceHomAction_continuous A B hA hB

/-- The proved finite-generator action is continuous in the literal
representation coordinates of the original free relation cover. -/
theorem originalInternalHomAction_continuous_of_finiteGenerated [Module.Finite R A] :
    Continuous (fun z : G × (Rep.ihom A).obj B => ((Rep.ihom A).obj B).ρ z.1 z.2) := by
  letI : TopologicalSpace ((CategoryTheory.ihom A).obj B) :=
    inferInstanceAs (TopologicalSpace ((Rep.ihom A).obj B))
  letI : DiscreteTopology ((CategoryTheory.ihom A).obj B) :=
    inferInstanceAs (DiscreteTopology ((Rep.ihom A).obj B))
  exact finiteGeneratedSourceHomAction_continuous A B hA hB

end
end Dubon2026
