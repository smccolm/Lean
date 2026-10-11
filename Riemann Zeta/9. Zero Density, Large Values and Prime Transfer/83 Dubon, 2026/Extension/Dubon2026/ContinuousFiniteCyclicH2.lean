import Dubon2026.ContinuousDiscreteH2Comparison
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic

/-! # Genuine finite cyclic continuous H2 and the original coefficient norm -/

namespace Dubon2026
noncomputable section
open CategoryTheory

variable {R G : Type} [CommRing R] [CommGroup G] [Fintype G]
  [TopologicalSpace R] [TopologicalSpace G] [DiscreteTopology G]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)

/-- The original finite cyclic invariant-to-H2 map, transported through the
proved continuous/algebraic comparison for the actual discrete group topology. -/
def continuousFiniteCyclicH2Pi :
    LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap →ₗ[R]
      ContinuousRepresentationH2 A hA :=
  (continuousDiscreteH2Equiv A hA).symm.toLinearMap.comp
    (Rep.FiniteCyclicGroup.groupCohomologyπEven A g hg 2 (by decide)).hom

/-- Forgetting continuity returns the exact pinned finite cyclic class. -/
theorem continuousFiniteCyclicH2Pi_algebraic
    (x : LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap) :
    continuousH2ToAlgebraic A hA (continuousFiniteCyclicH2Pi A hA g hg x) =
      Rep.FiniteCyclicGroup.groupCohomologyπEven A g hg 2 (by decide) x := by
  exact (continuousDiscreteH2Equiv A hA).apply_symm_apply _

/-- The actual continuous finite cyclic H2 class vanishes exactly when the
original invariant coefficient lies in the original representation norm range. -/
theorem continuousFiniteCyclicH2Pi_eq_zero_iff
    (x : LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap) :
    continuousFiniteCyclicH2Pi A hA g hg x = 0 ↔
      x.val ∈ LinearMap.range A.norm.hom.toLinearMap := by
  rw [← (continuousH2ToAlgebraic_injective A hA).eq_iff,
    continuousFiniteCyclicH2Pi_algebraic, map_zero]
  exact Rep.FiniteCyclicGroup.groupCohomologyπEven_eq_zero_iff A g hg 2 (by decide) x

/-- Two genuine invariant coefficients give the same original continuous H2
class precisely when their difference is an actual norm. -/
theorem continuousFiniteCyclicH2Pi_eq_iff
    (x y : LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap) :
    continuousFiniteCyclicH2Pi A hA g hg x = continuousFiniteCyclicH2Pi A hA g hg y ↔
      x.val - y.val ∈ LinearMap.range A.norm.hom.toLinearMap := by
  rw [← sub_eq_zero, ← map_sub, continuousFiniteCyclicH2Pi_eq_zero_iff]
  rfl

/-- Every actual continuous H2 class on the finite cyclic group comes from
an invariant coefficient, using the pinned projective-resolution computation. -/
theorem continuousFiniteCyclicH2Pi_surjective :
    Function.Surjective (continuousFiniteCyclicH2Pi A hA g hg) := by
  have hp : Function.Surjective
      (Rep.FiniteCyclicGroup.groupCohomologyπEven A g hg 2 (by decide)) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  exact (continuousDiscreteH2Equiv A hA).symm.surjective.comp hp

end
end Dubon2026
