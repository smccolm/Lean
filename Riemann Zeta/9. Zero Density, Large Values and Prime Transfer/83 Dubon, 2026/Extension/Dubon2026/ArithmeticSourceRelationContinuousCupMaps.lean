import Dubon2026.ArithmeticSourceRelationCupMaps
import Dubon2026.OriginalRelationCupContinuous

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module Submodule.Quotient.module
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Use the original arithmetic union inclusion. -/
local instance sourceContinuousCupUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Use the actual finite stage inclusion. -/
local instance sourceContinuousCupFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

variable [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]

/-- Integer scalar multiplication on the original discrete Hom is continuous. -/
local instance sourceContinuousCupHomContinuousSMul :
    @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
      (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology

/-- The original full arithmetic class continuous H2 quotient. -/
abbrev arithmeticSourceRelationContinuousH2 :=
  let D := arithmeticClassesModOutsideColimitRep ℚ Ω a ha
  letI : @ContinuousSMul ℤ D D.hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ D D.hV2.toSMul _ _ continuous_of_discreteTopology
  ContinuousRepresentationH2 D (arithmeticClassesModOutsideColimitAction_continuous ℚ Ω a ha)

/-- The actual source-class cup after its literal full-class coefficient
comparison, retaining the original continuous H2 quotient. -/
def arithmeticSourceRelationContinuousCupClass [Finite B]
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B))
    (x : arithmeticSourceRelationContinuousH1 Ω a P B) :
    arithmeticSourceRelationContinuousH2 Ω a ha := by
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
  exact continuousH1Cup A U D (originalInternalHomEvaluation A D)
      (originalInternalHomEvaluation_equivariant A D) continuous_of_discreteTopology
      hA hU hD x ((continuousRepresentationCoboundariesOne U hU).mkQ u)

/-- The actual relation morphism applied to the continuous connecting class. -/
def arithmeticSourceRelationContinuousConnectingClass
    (φ : (arithmeticSourceRelationPresentation Ω a P B).X₁ ⟶
      arithmeticClassesModOutsideColimitRep ℚ Ω a ha)
    (x : arithmeticSourceRelationContinuousH1 Ω a P B) :
    arithmeticSourceRelationContinuousH2 Ω a ha := by
  let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(P/ℚ) := AlgEquiv.restrictNormalHom P
  let X : ShortComplex (Rep ℤ Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ)) := {
    X₁ := Rep.res π (originalRelationModule B)
    X₂ := Rep.res π (Rep.free ℤ Gal(P/ℚ) B)
    X₃ := Rep.res π B
    f := (Rep.resFunctor π).map (originalRelationInclusion B)
    g := (Rep.resFunctor π).map (originalRelationFreeCover B)
    zero := ((originalRelationShortComplex B).map (Rep.resFunctor π)).zero }
  let D := arithmeticClassesModOutsideColimitRep ℚ Ω a ha
  letI : TopologicalSpace X.X₁ := ⊥
  letI : DiscreteTopology X.X₁ := ⟨rfl⟩
  letI : TopologicalSpace X.X₂ := ⊥
  letI : DiscreteTopology X.X₂ := ⟨rfl⟩
  letI : TopologicalSpace X.X₃ := ⊥
  letI : DiscreteTopology X.X₃ := ⟨rfl⟩
  letI : @ContinuousSMul ℤ X.X₁ (X.X₁).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ X.X₁ (X.X₁).hV2.toSMul _ _ continuous_of_discreteTopology
  letI : @ContinuousSMul ℤ X.X₂ (X.X₂).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ X.X₂ (X.X₂).hV2.toSMul _ _ continuous_of_discreteTopology
  letI : @ContinuousSMul ℤ X.X₃ (X.X₃).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ X.X₃ (X.X₃).hV2.toSMul _ _ continuous_of_discreteTopology
  letI : @ContinuousSMul ℤ D (D).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ D (D).hV2.toSMul _ _ continuous_of_discreteTopology
  let hA := arithmeticFiniteStageRepresentationAction_continuous ℚ Ω a P (originalRelationModule B)
  let hB := arithmeticFiniteStageRepresentationAction_continuous ℚ Ω a P (Rep.free ℤ Gal(P/ℚ) B)
  let hC := arithmeticFiniteStageRepresentationAction_continuous ℚ Ω a P B
  let hD := arithmeticClassesModOutsideColimitAction_continuous ℚ Ω a ha
  let hX : X.ShortExact := originalRelationGroupChange_shortExact π B
  exact continuousCoefficientH2Map X.X₁ D φ.hom.toLinearMap continuous_of_discreteTopology
    (Rep.hom_comm_apply φ) hA hD (continuousShortComplexConnectingMap X hX hA hB hC x)

end
end Dubon2026
