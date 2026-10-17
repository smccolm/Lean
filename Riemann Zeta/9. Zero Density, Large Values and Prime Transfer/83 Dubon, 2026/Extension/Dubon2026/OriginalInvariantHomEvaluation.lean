import Dubon2026.OriginalInternalHomEvaluation
import Dubon2026.ContinuousAlgebraicH2Coefficient
import Dubon2026.ContinuousInvariantH2Pairing

/-! # Invariant evaluation is the literal original coefficient morphism

This identifies continuous H2 evaluation with the algebraic coefficient
image, preserving the actual relation obstruction used by DUB-17's
finite class criterion.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2
variable {R G : Type} [CommRing R] [Group G] (A D : Rep.{0} R G)

/-- An actual invariant internal Hom coefficient gives its literal
equivariant coefficient morphism, without an equivariance hypothesis. -/
def originalInvariantHomMorphism (w : ((Rep.ihom A).obj D).ρ.invariants) : A ⟶ D :=
  Rep.ofHom {
    toLinearMap := (originalInternalHomEvaluation A D).flip w.val
    isIntertwining' g := by
      apply LinearMap.ext
      intro a
      simpa only [w.property g] using originalInternalHomEvaluation_equivariant A D g a w.val }

/-- The constructed coefficient morphism is the original Hom coefficient
applied to the original element. -/
theorem originalInvariantHomMorphism_apply
    (w : ((Rep.ihom A).obj D).ρ.invariants) (a : A) :
    (originalInvariantHomMorphism A D w).hom a = (show A →ₗ[R] D from w.val) a := rfl

variable [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul R A]
  [TopologicalSpace D] [IsTopologicalAddGroup D] [ContinuousSMul R D]
  [TopologicalSpace ((Rep.ihom A).obj D)] [DiscreteTopology ((Rep.ihom A).obj D)]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hD : Continuous (fun z : G × D => D.ρ z.1 z.2))

/-- Forgetting continuity sends invariant evaluation to the original
algebraic H2 map of the same literal coefficient morphism. -/
theorem originalInvariantHomH2Evaluation_toAlgebraic
    (w : ((Rep.ihom A).obj D).ρ.invariants) (x : ContinuousRepresentationH2 A hA) :
    continuousH2ToAlgebraic D hD
      (continuousInvariantRightH2Map A ((Rep.ihom A).obj D) D
        (originalInternalHomEvaluation A D) (originalInternalHomEvaluation_equivariant A D)
        continuous_of_discreteTopology hA hD w x) =
    groupCohomology.map (MonoidHom.id G) (originalInvariantHomMorphism A D w) 2
      (continuousH2ToAlgebraic A hA x) := by
  exact continuousH2Coefficient_toAlgebraic A D (originalInvariantHomMorphism A D w)
    continuous_of_discreteTopology hA hD x

end
end Dubon2026
