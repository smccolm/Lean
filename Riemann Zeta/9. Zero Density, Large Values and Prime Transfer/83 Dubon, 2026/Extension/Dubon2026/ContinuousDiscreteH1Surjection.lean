import Dubon2026.ContinuousAlgebraicH1Map

/-! # Every finite-stage H1 class retains a continuous representative

The pinned cocycle surjection and the original discrete group topology
supply the exact representative needed by DUB-17's finite relation criterion.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G] [DiscreteTopology G]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))

omit [IsTopologicalGroup G] in
/-- Every original algebraic H1 class over the discrete stage is represented
by the very same cocycle in continuous H1. -/
theorem continuousH1ToAlgebraic_surjective :
    Function.Surjective (continuousH1ToAlgebraic A hA) := by
  intro y
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (groupCohomology.H1π A)).mp inferInstance y
  exact ⟨(continuousRepresentationCoboundariesOne A hA).mkQ
    ⟨z, continuous_of_discreteTopology⟩, rfl⟩

end
end Dubon2026
