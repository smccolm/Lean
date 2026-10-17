import Dubon2026.ArithmeticSourceRelationContinuousCupMaps
import Dubon2026.ArithmeticFiniteStageTowerComparison
import Dubon2026.ContinuousCohomologyRestriction

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module Submodule.Quotient.module
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Use the original arithmetic union inclusion. -/
local instance sourceContinuousFiniteUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Use the actual finite stage inclusion. -/
local instance sourceContinuousFiniteFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

variable [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]

/-- Integer scalar multiplication on the original discrete Hom is continuous. -/
local instance sourceContinuousFiniteHomContinuousSMul :
    @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
      (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology

/-- Continuous H1 at the exact finite stage descended from the source cocycle. -/
abbrev arithmeticSourceRelationStageContinuousH1
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B))
    (r : ArithmeticSourceClassRelationData Ω a ha P B c) :=
  let BN := arithmeticSourceClassRelationStageCoefficient Ω a ha P B c r
  letI : TopologicalSpace BN := ⊥
  letI : DiscreteTopology BN := ⟨rfl⟩
  letI : @ContinuousSMul ℤ BN (BN).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ BN (BN).hV2.toSMul _ _ continuous_of_discreteTopology
  ContinuousRepresentationH1 BN continuous_of_discreteTopology

/-- Inflate the same finite H1 input along the continuous arithmetic restriction
and the literal identity-on-values source-stage coefficient comparison. -/
def arithmeticSourceRelationFiniteContinuousH1Inflation
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B))
    (r : ArithmeticSourceClassRelationData Ω a ha P B c)
    (y : arithmeticSourceRelationStageContinuousH1 Ω a ha P B c r) :
    arithmeticSourceRelationContinuousH1 Ω a P B := by
  let BN := arithmeticSourceClassRelationStageCoefficient Ω a ha P B c r
  letI : TopologicalSpace BN := ⊥
  letI : DiscreteTopology BN := ⟨rfl⟩
  letI : @ContinuousSMul ℤ BN (BN).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ BN (BN).hV2.toSMul _ _ continuous_of_discreteTopology
  let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(r.stage/ℚ) :=
    AlgEquiv.restrictNormalHom r.stage
  let hπ := InfiniteGalois.restrictNormalHom_continuous r.stage.toIntermediateField
  let σ : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(P/ℚ) :=
    AlgEquiv.restrictNormalHom P
  let A := Rep.res σ B
  let β := arithmeticFiniteRestrictionTowerComparison ℚ Ω a P r.stage r.le_stage B
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : @ContinuousSMul ℤ A (A).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ A (A).hV2.toSMul _ _ continuous_of_discreteTopology
  let hBN : Continuous (fun z : Gal(r.stage/ℚ) × BN => BN.ρ z.1 z.2) :=
    continuous_of_discreteTopology
  let hA := arithmeticFiniteStageRepresentationAction_continuous ℚ Ω a P B
  exact continuousCoefficientH1Map (Rep.res π BN) A β.hom.toLinearMap
    continuous_of_discreteTopology (Rep.hom_comm_apply β)
    (restrictedCoefficientAction_continuous BN π hπ hBN) hA
    (continuousRepresentationH1Restriction BN hBN π hπ y)

/-- The actual finite relation connecting obstruction, transported into the
original continuous class H2 quotient through the literal colimit inclusion. -/
def arithmeticSourceRelationFiniteContinuousObstruction
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B))
    (r : ArithmeticSourceClassRelationData Ω a ha P B c)
    (y : arithmeticSourceRelationStageContinuousH1 Ω a ha P B c r) :
    arithmeticSourceRelationContinuousH2 Ω a ha := by
  let BN := arithmeticSourceClassRelationStageCoefficient Ω a ha P B c r
  letI : TopologicalSpace BN := ⊥
  letI : DiscreteTopology BN := ⟨rfl⟩
  letI : @ContinuousSMul ℤ BN (BN).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ BN (BN).hV2.toSMul _ _ continuous_of_discreteTopology
  let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(r.stage/ℚ) :=
    AlgEquiv.restrictNormalHom r.stage
  let hπ := InfiniteGalois.restrictNormalHom_continuous r.stage.toIntermediateField
  let X : ShortComplex (Rep ℤ Gal(r.stage/ℚ)) := {
    X₁ := originalRelationModule BN
    X₂ := Rep.free ℤ Gal(r.stage/ℚ) BN
    X₃ := BN
    f := originalRelationInclusion BN
    g := originalRelationFreeCover BN
    zero := (originalRelationShortComplex BN).zero }
  let C := arithmeticClassesModOutsideStageRep ℚ Ω a ha r.stage
  let D := arithmeticClassesModOutsideColimitRep ℚ Ω a ha
  let η := arithmeticSourceClassRelationStageHom Ω a ha P B c r
  let j := coefficientRepresentationColimitOf _
    (arithmeticGlobalClassesModOutsideStageTransition ℚ Ω a ha) r.stage
  letI : TopologicalSpace X.X₁ := ⊥
  letI : DiscreteTopology X.X₁ := ⟨rfl⟩
  letI : @ContinuousSMul ℤ X.X₁ (X.X₁).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ X.X₁ (X.X₁).hV2.toSMul _ _ continuous_of_discreteTopology
  letI : TopologicalSpace X.X₂ := ⊥
  letI : DiscreteTopology X.X₂ := ⟨rfl⟩
  letI : @ContinuousSMul ℤ X.X₂ (X.X₂).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ X.X₂ (X.X₂).hV2.toSMul _ _ continuous_of_discreteTopology
  letI : TopologicalSpace X.X₃ := ⊥
  letI : DiscreteTopology X.X₃ := ⟨rfl⟩
  letI : @ContinuousSMul ℤ X.X₃ (X.X₃).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ X.X₃ (X.X₃).hV2.toSMul _ _ continuous_of_discreteTopology
  letI : TopologicalSpace C := ⊥
  letI : DiscreteTopology C := ⟨rfl⟩
  letI : @ContinuousSMul ℤ C (C).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ C (C).hV2.toSMul _ _ continuous_of_discreteTopology
  letI : @ContinuousSMul ℤ D D.hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ D D.hV2.toSMul _ _ continuous_of_discreteTopology
  let hX₁ : Continuous (fun z : Gal(r.stage/ℚ) × X.X₁ => X.X₁.ρ z.1 z.2) :=
    continuous_of_discreteTopology
  let hX₂ : Continuous (fun z : Gal(r.stage/ℚ) × X.X₂ => X.X₂.ρ z.1 z.2) :=
    continuous_of_discreteTopology
  let hBN : Continuous (fun z : Gal(r.stage/ℚ) × BN => BN.ρ z.1 z.2) :=
    continuous_of_discreteTopology
  let hC : Continuous (fun z : Gal(r.stage/ℚ) × C => C.ρ z.1 z.2) :=
    continuous_of_discreteTopology
  let hD := arithmeticClassesModOutsideColimitAction_continuous ℚ Ω a ha
  exact continuousCoefficientH2Map (Rep.res π C) D j.hom.toLinearMap
    continuous_of_discreteTopology (Rep.hom_comm_apply j)
    (restrictedCoefficientAction_continuous C π hπ hC) hD
    (continuousRepresentationH2Restriction C hC π hπ
      (continuousCoefficientH2Map X.X₁ C η.hom.toLinearMap
        continuous_of_discreteTopology (Rep.hom_comm_apply η) hX₁ hC
        (continuousShortComplexConnectingMap X (originalRelationShortComplex_shortExact BN)
          hX₁ hX₂ hBN y)))

end
end Dubon2026
