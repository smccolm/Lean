import Dubon2026.ContinuousAlgebraicH1Map
import Dubon2026.ContinuousDiscreteH2Comparison
import Dubon2026.ContinuousCoefficientConnectingMap
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

/-! # The continuous connecting map is the original algebraic connecting map

The pinned cocycle formula identifies the two actual maps using the same
lift and boundary. This comparison is needed to bring the finite relation
obstruction into DUB-17's continuous cup/connecting duality argument.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (X : ShortComplex (Rep.{0} R G)) (hX : X.ShortExact)
  [TopologicalSpace X.X₁] [IsTopologicalAddGroup X.X₁] [ContinuousSMul R X.X₁]
  [TopologicalSpace X.X₂] [DiscreteTopology X.X₂] [ContinuousSMul R X.X₂]
  [TopologicalSpace X.X₃] [DiscreteTopology X.X₃] [ContinuousSMul R X.X₃]
  (hA : Continuous (fun z : G × X.X₁ => X.X₁.ρ z.1 z.2))
  (hB : Continuous (fun z : G × X.X₂ => X.X₂.ρ z.1 z.2))
  (hC : Continuous (fun z : G × X.X₃ => X.X₃.ρ z.1 z.2))

/-- The actual continuous connecting map of an original short exact
coefficient sequence, with all linear exactness premises derived. -/
def continuousShortComplexConnectingMap :
    ContinuousRepresentationH1 X.X₃ hC →ₗ[R] ContinuousRepresentationH2 X.X₁ hA :=
  continuousCoefficientConnectingMap X.X₁ X.X₂ X.X₃ X.f.hom.toLinearMap
    ((Rep.mono_iff_injective X.f).mp hX.mono_f) (Rep.hom_comm_apply X.f)
    X.g.hom.toLinearMap ((Rep.epi_iff_surjective X.g).mp hX.epi_g)
    (Rep.hom_comm_apply X.g)
    (hX.exact.map (forget₂ (Rep R G) (ModuleCat R))).moduleCat_range_eq_ker hA hB hC

/-- Forgetting continuity commutes with the original H1-to-H2 connecting
map. The identity is proved from actual cocycles, without a comparison hypothesis. -/
theorem continuousShortComplexConnectingMap_toAlgebraic
    (x : ContinuousRepresentationH1 X.X₃ hC) :
    continuousH2ToAlgebraic X.X₁ hA (continuousShortComplexConnectingMap X hX hA hB hC x) =
      groupCohomology.δ hX 1 2 rfl (continuousH1ToAlgebraic X.X₃ hC x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    let hf := (Rep.mono_iff_injective X.f).mp hX.mono_f
    let hg := (Rep.epi_iff_surjective X.g).mp hX.epi_g
    let he := (hX.exact.map (forget₂ (Rep R G) (ModuleCat R))).moduleCat_range_eq_ker
    let y := coefficientConnectingOneLift X.X₂ X.X₃ X.g.hom.toLinearMap hg c
    let z := coefficientConnectingTwoCocycle X.X₁ X.X₂ X.X₃ X.f.hom.toLinearMap hf
      (Rep.hom_comm_apply X.f) X.g.hom.toLinearMap hg (Rep.hom_comm_apply X.g) he hB c
    have hy : X.g.hom ∘ y = c.val := by
      funext g
      exact coefficientConnectingOneLift_project X.X₂ X.X₃ X.g.hom.toLinearMap hg c g
    have hz : X.f.hom ∘ z.val = groupCohomology.d₁₂ X.X₂ y := by
      funext g
      exact coefficientConnectingTwoCocycle_map X.X₁ X.X₂ X.X₃ X.f.hom.toLinearMap hf
        (Rep.hom_comm_apply X.f) X.g.hom.toLinearMap hg (Rep.hom_comm_apply X.g) he hB c g
    exact (groupCohomology.δ₁_apply hX c.val y hy z.val hz).symm

end
end Dubon2026
