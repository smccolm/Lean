import Dubon2026.ContinuousAlgebraicH2Coefficient
import Dubon2026.ContinuousCohomologyRestriction

/-! # The actual continuous group/coefficient map retains its finite class

This literal comparison identifies the finite continuous obstruction with
the algebraic class tested by DUB-17's scalar relation criterion. It makes
no injectivity claim for arithmetic continuous-to-algebraic H2.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
variable {R G H : Type} [CommRing R] [Group G] [Group H]
  [TopologicalSpace R] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]
  (π : G →* H) (hπ : Continuous π) (A : Rep R H) (B : Rep R G)
  [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul R A]
  [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul R B]
  (hA : Continuous (fun z : H × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))

/-- Forgetting continuity preserves the original group restriction and
coefficient image on the same actual H2 cocycle. -/
theorem continuousH2_groupCoefficient_toAlgebraic (φ : Rep.res π A ⟶ B)
    (x : ContinuousRepresentationH2 A hA) :
    continuousH2ToAlgebraic B hB
      (continuousCoefficientH2Map (Rep.res π A) B φ.hom.toLinearMap
        continuous_of_discreteTopology (Rep.hom_comm_apply φ)
        (restrictedCoefficientAction_continuous A π hπ hA) hB
        (continuousRepresentationH2Restriction A hA π hπ x)) =
      groupCohomology.map π φ 2 (continuousH2ToAlgebraic A hA x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    rw [continuousRepresentationH2Restriction_mk, continuousCoefficientH2Map_mk,
      continuousH2ToAlgebraic_mk, continuousH2ToAlgebraic_mk,
      groupCohomology.H2π_comp_map_apply]
    rfl

end
end Dubon2026
