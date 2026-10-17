import Dubon2026.ArithmeticSourceScalarContinuousMaps
import Dubon2026.ArithmeticSourceScalarStageDiagramSquare
import Dubon2026.ContinuousShortComplexObstructionSquare

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module Submodule.Quotient.module
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Use the original arithmetic union inclusion. -/
local instance sourceScalarConnectingUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Use the actual finite stage inclusion. -/
local instance sourceScalarConnectingFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

variable [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]

/-- Integer scalar multiplication on the original discrete Hom is continuous. -/
local instance sourceScalarConnectingHomContinuousSMul :
    @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
      (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology

/-- The actual enlarged-stage presentation diagram and proved
coefficient square identify its continuous obstruction with the connecting
image in the original source presentation. -/
theorem arithmeticSourceClassRelationData_scalar_continuous_connecting
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B))
    (r : ArithmeticSourceClassRelationData Ω a ha P B c)
    (F : OriginalUnramifiedGaloisStage (Ω := Ω) a) (i : r.stage →ₐ[ℚ] F.val)
    (L : OriginalUnramifiedGaloisStage (Ω := Ω) a)
    (hFL : F.val.toIntermediateField ≤ L.val.toIntermediateField)
    (hi : ∀ x : r.stage, (i x : Ω) = (x.val : Ω))
    (y : arithmeticSourceScalarStageContinuousH1 Ω a ha P B c r F i L hFL) :
    arithmeticSourceRelationContinuousConnectingClass Ω a ha P B r.relation
      (arithmeticSourceScalarContinuousH1Inflation Ω a ha P B c r F i L hFL hi y) =
      arithmeticSourceScalarContinuousObstruction Ω a ha P B c r F i L hFL y := by
  letI : Algebra L.val (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
    (IntermediateField.inclusion (originalUnramifiedGaloisStage_le_union a L)).toAlgebra
  letI : IsScalarTower ℚ L.val (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
    IsScalarTower.of_algHom (IntermediateField.inclusion (originalUnramifiedGaloisStage_le_union a L))
  let BL := arithmeticSourceScalarStageCoefficient Ω a ha P B c r F i L hFL
  letI : TopologicalSpace BL := ⊥
  letI : DiscreteTopology BL := ⟨rfl⟩
  letI : @ContinuousSMul ℤ BL (BL).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ BL (BL).hV2.toSMul _ _ continuous_of_discreteTopology
  let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(L.val/ℚ) :=
    AlgEquiv.restrictNormalHom L.val
  let hπ := originalScalarStageRestriction_continuous Ω a L
  let X : ShortComplex (Rep ℤ Gal(L.val/ℚ)) := {
    X₁ := originalRelationModule BL
    X₂ := Rep.free ℤ Gal(L.val/ℚ) BL
    X₃ := BL
    f := originalRelationInclusion BL
    g := originalRelationFreeCover BL
    zero := (originalRelationShortComplex BL).zero }
  let C := arithmeticOriginalStageClassRep Ω a ha L
  let D := arithmeticClassesModOutsideColimitRep ℚ Ω a ha
  let η := arithmeticSourceScalarStageRelationTransport Ω a ha P B c r F i L hFL
  let j := arithmeticOriginalStageClassToColimit Ω a ha L
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
  let hX₁ : Continuous (fun z : Gal(L.val/ℚ) × X.X₁ => X.X₁.ρ z.1 z.2) :=
    continuous_of_discreteTopology
  let hX₂ : Continuous (fun z : Gal(L.val/ℚ) × X.X₂ => X.X₂.ρ z.1 z.2) :=
    continuous_of_discreteTopology
  let hBL : Continuous (fun z : Gal(L.val/ℚ) × BL => BL.ρ z.1 z.2) :=
    continuous_of_discreteTopology
  let hC : Continuous (fun z : Gal(L.val/ℚ) × C => C.ρ z.1 z.2) :=
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
    arithmeticSourceScalarStageDiagram Ω a ha P B c r F i L hFL hi
  have hs := arithmeticSourceScalarStageDiagram_square Ω a ha P B c r F i L hFL hi
  exact continuousShortComplex_obstruction_square π hπ X Y e
    (originalRelationShortComplex_shortExact BL) (originalRelationGroupChange_shortExact σ B)
    hX₁ hX₂ hBL hY₁ hY₂ hY₃ C D hC hD η j r.relation hs y

end
end Dubon2026
