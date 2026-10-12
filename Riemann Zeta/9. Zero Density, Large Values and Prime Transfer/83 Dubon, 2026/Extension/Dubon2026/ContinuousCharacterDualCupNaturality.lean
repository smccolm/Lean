import Dubon2026.FiniteCharacterDualCupAdjunction

/-! # Original character-dual H1 cups and coefficient naturality

The actual finite coefficient action determines its continuous character
dual. Literal precomposition gives the cup identity used to test split-module
classes by their scalar coordinates in DUB-17's local duality argument.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] characterDualSequenceContinuousSMul

variable {k G : Type} [Field k] [Group G]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))

/-- The original H1 cup with its genuine character-valued coefficient dual,
whose action continuity is derived from the original finite coefficient. -/
def continuousCharacterDualH1Cup :
    ContinuousRepresentationH1 A hA →ₗ[k]
      ContinuousRepresentationH1 (characterDualCoefficientRep A χ)
        (finiteCharacterDualAction_continuous A χ hA hχ) →ₗ[k]
      ContinuousRepresentationH2 (coefficientCharacterRep χ)
        (coefficientCharacterAction_continuous χ hχ) :=
  continuousH1Cup A (characterDualCoefficientRep A χ) (coefficientCharacterRep χ)
    (characterDualEvaluation A χ) (characterDualEvaluation_equivariant A χ)
    continuous_of_discreteTopology hA (finiteCharacterDualAction_continuous A χ hA hχ)
    (coefficientCharacterAction_continuous χ hχ)

/-- This specialized cup keeps exactly the original continuous cup cocycle. -/
theorem continuousCharacterDualH1Cup_mk (c : continuousRepresentationCocyclesOne A)
    (u : continuousRepresentationCocyclesOne (characterDualCoefficientRep A χ)) :
    continuousCharacterDualH1Cup A χ hχ hA (Submodule.Quotient.mk c) (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk (continuousOneCocycleCup A (characterDualCoefficientRep A χ)
        (coefficientCharacterRep χ) (characterDualEvaluation A χ)
        (characterDualEvaluation_equivariant A χ) continuous_of_discreteTopology
        (finiteCharacterDualAction_continuous A χ hA hχ) c u) := rfl

variable (B : Rep.{0} k G) [Finite B] [TopologicalSpace B] [DiscreteTopology B]
  [TopologicalSpace (characterDualCoefficientRep B χ)]
  [DiscreteTopology (characterDualCoefficientRep B χ)]
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))
  (φ : A →ₗ[k] B) (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))

/-- The actual coefficient map and literal dual precomposition are adjoint
under the original continuous H1 cup. No cohomological naturality premise is assumed. -/
theorem continuousCharacterDualH1Cup_naturality
    (x : ContinuousRepresentationH1 A hA)
    (y : ContinuousRepresentationH1 (characterDualCoefficientRep B χ)
      (finiteCharacterDualAction_continuous B χ hB hχ)) :
    continuousCharacterDualH1Cup A χ hχ hA x
      (continuousCoefficientH1Map (characterDualCoefficientRep B χ) (characterDualCoefficientRep A χ)
        (characterDualCoefficientMap A B χ φ) continuous_of_discreteTopology
        (characterDualCoefficientMap_equivariant A B χ φ hφρ)
        (finiteCharacterDualAction_continuous B χ hB hχ)
        (finiteCharacterDualAction_continuous A χ hA hχ) y) =
      continuousCharacterDualH1Cup B χ hχ hB
        (continuousCoefficientH1Map A B φ continuous_of_discreteTopology hφρ hA hB x) y := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    induction y using Submodule.Quotient.induction_on with
    | _ u =>
      rw [continuousCoefficientH1Map_mk, continuousCoefficientH1Map_mk,
        continuousCharacterDualH1Cup_mk, continuousCharacterDualH1Cup_mk]
      congr 1
      apply Subtype.ext
      apply Subtype.ext
      funext z
      change characterDualEvaluation A χ (c.val z.1)
          ((characterDualCoefficientRep A χ).ρ z.1
            (characterDualCoefficientMap A B χ φ (u.val z.2))) =
        characterDualEvaluation B χ (φ (c.val z.1))
          ((characterDualCoefficientRep B χ).ρ z.1 (u.val z.2))
      rw [← characterDualCoefficientMap_equivariant A B χ φ hφρ]
      exact (characterDualEvaluation_precompose A B χ φ _ _).symm

end
end Dubon2026
