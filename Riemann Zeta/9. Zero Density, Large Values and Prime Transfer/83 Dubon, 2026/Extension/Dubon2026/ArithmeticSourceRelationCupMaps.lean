import Dubon2026.OriginalRelationCupExplicitLift
import Dubon2026.ArithmeticSourceClassScalarStage
import Dubon2026.ArithmeticFreeClassHomContinuity
/-! # The actual source-class cup is the original relation obstruction

Consume the free-cover lift already constructed in the original source-cocycle
data. The existing explicit-boundary adjunction identifies its continuous cup
with the algebraic relation connecting class, preserving the literal source
comparison and all Galois actions. This removes the class dual-sequence
exactness detour from DUB-17's reverse-localization dependency chain.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module Submodule.Quotient.module
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Use the original arithmetic union inclusion. -/
local instance sourceRelationCupUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Use the actual finite stage inclusion. -/
local instance sourceRelationCupFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

variable [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]

/-- Integer scalar multiplication on the original discrete Hom is continuous. -/
local instance sourceRelationCupHomContinuousSMul :
    @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
      (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology

/-- Continuous H1 of the actual finite-stage coefficient with its original
arithmetic Galois action and discrete coefficient topology. -/
abbrev arithmeticSourceRelationContinuousH1 :=
  let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(P/ℚ) :=
    AlgEquiv.restrictNormalHom P
  let A := Rep.res π B
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : @ContinuousSMul ℤ A A.hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ A A.hV2.toSMul _ _ continuous_of_discreteTopology
  ContinuousRepresentationH1 A (arithmeticFiniteStageRepresentationAction_continuous ℚ Ω a P B)

/-- The actual source-class cup after its literal full-class coefficient
comparison and the original continuous-to-algebraic H2 map. -/
def arithmeticSourceRelationCupClass [Finite B]
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B))
    (x : arithmeticSourceRelationContinuousH1 Ω a P B) :
    groupCohomology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha) 2 := by
  let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(P/ℚ) :=
    AlgEquiv.restrictNormalHom P
  let A := Rep.res π B
  let D := arithmeticClassesModOutsideColimitRep ℚ Ω a ha
  let U := (Rep.ihom A).obj D
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : TopologicalSpace U := ⊥
  letI : DiscreteTopology U := ⟨rfl⟩
  letI : @ContinuousSMul ℤ A A.hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ A A.hV2.toSMul _ _ continuous_of_discreteTopology
  letI : @ContinuousSMul ℤ D D.hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ D D.hV2.toSMul _ _ continuous_of_discreteTopology
  letI : @ContinuousSMul ℤ U U.hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ U U.hV2.toSMul _ _ continuous_of_discreteTopology
  let hA := arithmeticFiniteStageRepresentationAction_continuous ℚ Ω a P B
  let hD := arithmeticClassesModOutsideColimitAction_continuous ℚ Ω a ha
  let hU := originalInternalHomAction_continuous_of_finite A D hA hD
  let f : arithmeticFiniteCoefficientSourceClassHom Ω a ha P B ⟶ U :=
    arithmeticSourceClassHomComparison ℚ Ω a ha A
  let u := continuousCoefficientCocycleOneMap
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B) U
      f.hom.toLinearMap continuous_of_discreteTopology (Rep.hom_comm_apply f) c
  exact continuousH2ToAlgebraic D hD
    (continuousH1Cup A U D (originalInternalHomEvaluation A D)
      (originalInternalHomEvaluation_equivariant A D) continuous_of_discreteTopology
      hA hU hD x ((continuousRepresentationCoboundariesOne U hU).mkQ u))

/-- Apply the literal relation morphism to the original algebraic connecting
class of the same continuous H1 input. -/
def arithmeticSourceRelationConnectingClass
    (φ : (arithmeticSourceRelationPresentation Ω a P B).X₁ ⟶
      arithmeticClassesModOutsideColimitRep ℚ Ω a ha)
    (x : arithmeticSourceRelationContinuousH1 Ω a P B) :
    groupCohomology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha) 2 := by
  let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(P/ℚ) :=
    AlgEquiv.restrictNormalHom P
  let A := Rep.res π B
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : @ContinuousSMul ℤ A A.hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ A A.hV2.toSMul _ _ continuous_of_discreteTopology
  let hA := arithmeticFiniteStageRepresentationAction_continuous ℚ Ω a P B
  exact groupCohomology.map (MonoidHom.id _) φ 2
    (groupCohomology.δ (originalRelationGroupChange_shortExact π B) 1 2 rfl
      (continuousH1ToAlgebraic A hA x))

end
end Dubon2026
