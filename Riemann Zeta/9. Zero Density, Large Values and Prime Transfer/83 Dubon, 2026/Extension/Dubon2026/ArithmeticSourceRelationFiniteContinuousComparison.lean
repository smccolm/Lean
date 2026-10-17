import Dubon2026.ArithmeticSourceRelationStageH1Comparison
import Dubon2026.ContinuousFiniteObstructionComparison
import Dubon2026.OriginalRelationExtensionObstruction

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module Submodule.Quotient.module
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Use the original arithmetic union inclusion. -/
local instance sourceFiniteObstructionComparisonUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Use the actual finite stage inclusion. -/
local instance sourceFiniteObstructionComparisonFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

variable [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]

/-- Integer scalar multiplication on the original discrete Hom is continuous. -/
local instance sourceFiniteObstructionComparisonHomContinuousSMul :
    @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
      (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology

/-- Forget continuity on the literal original arithmetic class quotient. -/
def arithmeticSourceRelationContinuousH2ToAlgebraic
    (z : arithmeticSourceRelationContinuousH2 Ω a ha) :
    groupCohomology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha) 2 := by
  let D := arithmeticClassesModOutsideColimitRep ℚ Ω a ha
  letI : @ContinuousSMul ℤ D D.hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ D D.hV2.toSMul _ _ continuous_of_discreteTopology
  exact continuousH2ToAlgebraic D (arithmeticClassesModOutsideColimitAction_continuous ℚ Ω a ha) z

/-- The actual algebraic finite relation obstruction under its literal
arithmetic class-colimit inflation. -/
def arithmeticSourceRelationFiniteObstructionImage
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B))
    (r : ArithmeticSourceClassRelationData Ω a ha P B c)
    (y : groupCohomology (arithmeticSourceClassRelationStageCoefficient Ω a ha P B c r) 1) :
    groupCohomology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha) 2 := by
  let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(r.stage/ℚ) :=
    AlgEquiv.restrictNormalHom r.stage
  let BN := arithmeticSourceClassRelationStageCoefficient Ω a ha P B c r
  let C := arithmeticClassesModOutsideStageRep ℚ Ω a ha r.stage
  let η := arithmeticSourceClassRelationStageHom Ω a ha P B c r
  let j := coefficientRepresentationColimitOf _
    (arithmeticGlobalClassesModOutsideStageTransition ℚ Ω a ha) r.stage
  exact groupCohomology.map π j 2 ((originalRelationExtensionObstruction BN C η).hom y)

/-- The continuous obstruction retains exactly the finite algebraic H1
input and finite relation class used by the original scalar criterion. -/
theorem arithmeticSourceRelationFiniteContinuousObstruction_toAlgebraic
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B))
    (r : ArithmeticSourceClassRelationData Ω a ha P B c)
    (y : arithmeticSourceRelationStageContinuousH1 Ω a ha P B c r) :
    arithmeticSourceRelationContinuousH2ToAlgebraic Ω a ha
      (arithmeticSourceRelationFiniteContinuousObstruction Ω a ha P B c r y) =
      arithmeticSourceRelationFiniteObstructionImage Ω a ha P B c r
        (arithmeticSourceRelationStageH1ToAlgebraic Ω a ha P B c r y) := by
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
  exact continuousShortComplexObstruction_toAlgebraic π hπ X
    (originalRelationShortComplex_shortExact BN) C D hX₁ hX₂ hBN hC hD η j y

end
end Dubon2026
