import Dubon2026.ContinuousDiscreteH2Comparison
import Dubon2026.ContinuousCohomologyCoefficientMap
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-! # The original H2 coefficient map commutes with forgetting continuity

The same cocycle map is used on both sides. This identifies invariant
evaluation of the continuous relation obstruction with the actual
algebraic coefficient image used in DUB-17's finite relation criterion.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A B : Rep.{0} R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [IsTopologicalAddGroup B] [ContinuousSMul R B]
  (φ : A ⟶ B) (hφ : Continuous φ.hom)
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))

/-- The actual continuous and algebraic H2 coefficient maps preserve the
same original cocycle under the forgetful comparison. -/
theorem continuousH2Coefficient_toAlgebraic (x : ContinuousRepresentationH2 A hA) :
    continuousH2ToAlgebraic B hB
      (continuousCoefficientH2Map A B φ.hom.toLinearMap hφ (Rep.hom_comm_apply φ) hA hB x) =
    groupCohomology.map (MonoidHom.id G) φ 2 (continuousH2ToAlgebraic A hA x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    rw [continuousCoefficientH2Map_mk, continuousH2ToAlgebraic_mk,
      continuousH2ToAlgebraic_mk, groupCohomology.H2π_comp_map_apply]
    rfl

end
end Dubon2026
