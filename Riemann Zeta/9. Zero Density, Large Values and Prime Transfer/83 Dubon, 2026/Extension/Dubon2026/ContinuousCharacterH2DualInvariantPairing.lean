import Dubon2026.ContinuousCharacterDualCupNaturality
import Dubon2026.ContinuousInvariantH2Pairing

/-! # The original H2 pairing with actual character-dual invariants

Bilinearize the actual evaluation on original H2 and invariant character-dual
coefficients. Finite effacement and proved H1 duality will detect its H2
annihilator, supplying the missing local endpoint in DUB-17 global duality.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] characterDualSequenceContinuousSMul

variable {k G : Type} [Field k] [Group G]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [TopologicalSpace A] [DiscreteTopology A]
  (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))

/-- The original H2 class evaluates bilinearly against actual invariant
character-dual coefficients, via the original equivariant evaluation H2 map. -/
def continuousCharacterH2DualInvariantPairing :
    ContinuousRepresentationH2 A hA →ₗ[k]
      (characterDualCoefficientRep A χ).ρ.invariants →ₗ[k] ContinuousRepresentationH2 (coefficientCharacterRep χ)
        (coefficientCharacterAction_continuous χ hχ) where
  toFun x := {
    toFun w := continuousInvariantRightH2Map A (characterDualCoefficientRep A χ)
      (coefficientCharacterRep χ) (characterDualEvaluation A χ)
      (characterDualEvaluation_equivariant A χ)
      continuous_of_discreteTopology hA
      (coefficientCharacterAction_continuous χ hχ) w x
    map_add' u v := by
      induction x using Submodule.Quotient.induction_on with
      | _ c =>
        change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
        rfl
    map_smul' r u := by
      induction x using Submodule.Quotient.induction_on with
      | _ c =>
        change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
        rfl }
  map_add' x y := by
    apply LinearMap.ext
    intro w
    exact map_add (continuousInvariantRightH2Map A (characterDualCoefficientRep A χ)
      (coefficientCharacterRep χ) (characterDualEvaluation A χ)
      (characterDualEvaluation_equivariant A χ)
      continuous_of_discreteTopology hA
      (coefficientCharacterAction_continuous χ hχ) w) x y
  map_smul' r x := by
    apply LinearMap.ext
    intro w
    exact map_smul (continuousInvariantRightH2Map A (characterDualCoefficientRep A χ)
      (coefficientCharacterRep χ) (characterDualEvaluation A χ)
      (characterDualEvaluation_equivariant A χ)
      continuous_of_discreteTopology hA
      (coefficientCharacterAction_continuous χ hχ) w) r x

/-- The actual endpoint pairing is exactly the original invariant evaluation
on the same H2 quotient, with no change of cocycles or coboundaries. -/
theorem continuousCharacterH2DualInvariantPairing_apply
    (x : ContinuousRepresentationH2 A hA) (w : (characterDualCoefficientRep A χ).ρ.invariants) :
    continuousCharacterH2DualInvariantPairing A χ hχ hA x w =
    continuousInvariantRightH2Map A (characterDualCoefficientRep A χ)
      (coefficientCharacterRep χ) (characterDualEvaluation A χ)
      (characterDualEvaluation_equivariant A χ)
      continuous_of_discreteTopology hA
      (coefficientCharacterAction_continuous χ hχ) w x := rfl

end
end Dubon2026
