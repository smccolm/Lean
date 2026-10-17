import Dubon2026.ArithmeticSourceRelationContinuousFiniteMaps
import Dubon2026.ArithmeticSourceRelationContinuousDiagram
import Dubon2026.ContinuousShortComplexObstructionSquare

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module Submodule.Quotient.module
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Use the original arithmetic union inclusion. -/
local instance sourceContinuousFiniteConnectingUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Use the actual finite stage inclusion. -/
local instance sourceContinuousFiniteConnectingFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

variable [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]

/-- Integer scalar multiplication on the original discrete Hom is continuous. -/
local instance sourceContinuousFiniteConnectingHomContinuousSMul :
    @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
      (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology

/-- The actual tower diagram and derived coefficient square identify the
finite obstruction with the original continuous source connecting image. -/
theorem arithmeticSourceClassRelationData_finite_continuous_connecting
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B))
    (r : ArithmeticSourceClassRelationData Ω a ha P B c)
    (y : arithmeticSourceRelationStageContinuousH1 Ω a ha P B c r) :
    arithmeticSourceRelationContinuousConnectingClass Ω a ha P B r.relation
      (arithmeticSourceRelationFiniteContinuousH1Inflation Ω a ha P B c r y) =
      arithmeticSourceRelationFiniteContinuousObstruction Ω a ha P B c r y := by
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
  let σ : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(P/ℚ) :=
    AlgEquiv.restrictNormalHom P
  let Y : ShortComplex (Rep ℤ Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ)) := {
    X₁ := Rep.res σ (originalRelationModule B)
    X₂ := Rep.res σ (Rep.free ℤ Gal(P/ℚ) B)
    X₃ := Rep.res σ B
    f := (Rep.resFunctor σ).map (originalRelationInclusion B)
    g := (Rep.resFunctor σ).map (originalRelationFreeCover B)
    zero := ((originalRelationShortComplex B).map (Rep.resFunctor σ)).zero }
  letI : TopologicalSpace Y.X₁ := ⊥
  letI : DiscreteTopology Y.X₁ := ⟨rfl⟩
  letI : @ContinuousSMul ℤ Y.X₁ (Y.X₁).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ Y.X₁ (Y.X₁).hV2.toSMul _ _ continuous_of_discreteTopology
  letI : TopologicalSpace Y.X₂ := ⊥
  letI : DiscreteTopology Y.X₂ := ⟨rfl⟩
  letI : @ContinuousSMul ℤ Y.X₂ (Y.X₂).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ Y.X₂ (Y.X₂).hV2.toSMul _ _ continuous_of_discreteTopology
  letI : TopologicalSpace Y.X₃ := ⊥
  letI : DiscreteTopology Y.X₃ := ⟨rfl⟩
  letI : @ContinuousSMul ℤ Y.X₃ (Y.X₃).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ Y.X₃ (Y.X₃).hV2.toSMul _ _ continuous_of_discreteTopology
  let hY₁ := arithmeticFiniteStageRepresentationAction_continuous ℚ Ω a P (originalRelationModule B)
  let hY₂ := arithmeticFiniteStageRepresentationAction_continuous ℚ Ω a P (Rep.free ℤ Gal(P/ℚ) B)
  let hY₃ := arithmeticFiniteStageRepresentationAction_continuous ℚ Ω a P B
  let e : (Rep.resFunctor π).mapShortComplex.obj X ⟶ Y :=
    arithmeticSourceRelationFiniteDiagram Ω a ha P B c r
  have hs := arithmeticSourceRelationFiniteDiagram_square Ω a ha P B c r
  exact continuousShortComplex_obstruction_square π hπ X Y e
    (originalRelationShortComplex_shortExact BN) (originalRelationGroupChange_shortExact σ B)
    hX₁ hX₂ hBN hY₁ hY₂ hY₃ C D hC hD η j r.relation hs y

end
end Dubon2026
