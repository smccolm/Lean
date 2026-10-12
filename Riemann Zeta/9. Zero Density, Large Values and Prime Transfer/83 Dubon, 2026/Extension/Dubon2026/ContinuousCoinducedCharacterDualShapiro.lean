import Dubon2026.ContinuousCoinducedCharacterDualH1

/-! # The actual character-dual cup of continuous Shapiro classes

The original coinduced character dual is used on H1. Its actual cup is the
corestriction of the subgroup cup, as needed to carry split local annihilator
results to induced coefficients in DUB-17's local duality argument.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] characterDualSequenceContinuousSMul coinducedCoefficient_finite

variable {k G : Type} [Field k] [Group G]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (S : Subgroup G) [Fintype (G ⧸ S)] (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype A))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype A))]
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))]
  [TopologicalSpace (characterDualCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) χ)]
  [DiscreteTopology (characterDualCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) χ)]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2)) (hS : IsOpen (S : Set G))

/-- Scalars act continuously on the original discrete coinduced module. -/
local instance coinducedDualShapiroScalarContinuous :
    ContinuousSMul k (Rep.coind S.subtype (Rep.res S.subtype A)) :=
  ⟨continuous_of_discreteTopology⟩

/-- Scalars act continuously on the original discrete coinduced dual. -/
local instance coinducedDualShapiroDualScalarContinuous :
    ContinuousSMul k
      (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ))) :=
  ⟨continuous_of_discreteTopology⟩


/-- The actual character-dual cup on induced coefficients is the original
corestriction of the subgroup cup after both genuine continuous Shapiro maps. -/
theorem continuousCoinducedCharacterDualShapiro_cup
    (x : ContinuousRepresentationH1 (restrictedCoefficientRep A S.subtype)
      (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA))
    (y : ContinuousRepresentationH1 (restrictedCoefficientRep (characterDualCoefficientRep A χ) S.subtype)
      (restrictedCoefficientAction_continuous (characterDualCoefficientRep A χ)
        S.subtype continuous_subtype_val (finiteCharacterDualAction_continuous A χ hA hχ))) :
    continuousCharacterDualH1Cup (Rep.coind S.subtype (Rep.res S.subtype A)) χ hχ
      (finiteCoinducedCoefficientAction_continuous A S hA hS)
      (continuousCoinducedShapiroH1 A hA S hS x)
      (continuousCoinducedCharacterDualH1Equiv A S χ hχ hA hS
        (continuousCoinducedShapiroH1 (characterDualCoefficientRep A χ)
          (finiteCharacterDualAction_continuous A χ hA hχ) S hS y)) =
    continuousRepresentationH2Corestriction (coefficientCharacterRep χ)
      (coefficientCharacterAction_continuous χ hχ) S hS
      (continuousH1Cup (restrictedCoefficientRep A S.subtype)
        (restrictedCoefficientRep (characterDualCoefficientRep A χ) S.subtype)
        (restrictedCoefficientRep (coefficientCharacterRep χ) S.subtype)
        (characterDualEvaluation A χ) (fun g a ℓ => characterDualEvaluation_equivariant A χ g a ℓ)
        continuous_of_discreteTopology
        (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA)
        (restrictedCoefficientAction_continuous (characterDualCoefficientRep A χ)
          S.subtype continuous_subtype_val (finiteCharacterDualAction_continuous A χ hA hχ))
        (restrictedCoefficientAction_continuous (coefficientCharacterRep χ)
          S.subtype continuous_subtype_val (coefficientCharacterAction_continuous χ hχ)) x y) :=
  (continuousCoinducedCharacterDualH1Equiv_cup A S χ hχ hA hS _ _).trans
    (continuousCoinducedShapiroH1_cup A S χ hA (finiteCharacterDualAction_continuous A χ hA hχ)
      (coefficientCharacterAction_continuous χ hχ) hS x y)

end
end Dubon2026
