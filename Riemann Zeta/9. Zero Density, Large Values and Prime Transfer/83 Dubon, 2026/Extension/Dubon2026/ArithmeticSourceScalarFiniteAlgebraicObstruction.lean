import Dubon2026.ArithmeticSourceScalarFiniteContinuousObstruction
import Dubon2026.ContinuousFiniteCoefficientObstructionComparison

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module Submodule.Quotient.module
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Use the original arithmetic union inclusion. -/
local instance sourceScalarFiniteAlgebraicUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Use the actual finite stage inclusion. -/
local instance sourceScalarFiniteAlgebraicFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

variable [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]

/-- Integer scalar multiplication on the original discrete Hom is continuous. -/
local instance sourceScalarFiniteAlgebraicHomContinuousSMul :
    @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
      (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology



omit [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)] in
/-- The finite continuous scalar obstruction forgets to exactly the
original algebraic relation obstruction on the identical H1 input. -/
theorem arithmeticSourceScalarStageContinuousObstruction_toAlgebraic
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B))
    (r : ArithmeticSourceClassRelationData Ω a ha P B c)
    (F : OriginalUnramifiedGaloisStage (Ω := Ω) a) (i : r.stage →ₐ[ℚ] F.val)
    (L : OriginalUnramifiedGaloisStage (Ω := Ω) a)
    (hFL : F.val.toIntermediateField ≤ L.val.toIntermediateField)
    (y : arithmeticSourceScalarStageContinuousH1 Ω a ha P B c r F i L hFL) :
    let C := arithmeticOriginalStageClassRep Ω a ha L
    letI : TopologicalSpace C := ⊥
    letI : DiscreteTopology C := ⟨rfl⟩
    letI : @ContinuousSMul ℤ C C.hV2.toSMul inferInstance inferInstance :=
      @ContinuousSMul.mk ℤ C C.hV2.toSMul _ _ continuous_of_discreteTopology
    continuousH2ToAlgebraic C continuous_of_discreteTopology
      (arithmeticSourceScalarStageContinuousObstruction Ω a ha P B c r F i L hFL y) =
        (originalRelationExtensionObstruction
          (arithmeticSourceScalarStageCoefficient Ω a ha P B c r F i L hFL) C
          (arithmeticSourceScalarStageRelationTransport Ω a ha P B c r F i L hFL)).hom
            (arithmeticSourceScalarStageH1ToAlgebraic Ω a ha P B c r F i L hFL y) := by
  let BL := arithmeticSourceScalarStageCoefficient Ω a ha P B c r F i L hFL
  letI : TopologicalSpace BL := ⊥
  letI : DiscreteTopology BL := ⟨rfl⟩
  letI : @ContinuousSMul ℤ BL (BL).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ BL (BL).hV2.toSMul _ _ continuous_of_discreteTopology
  let X : ShortComplex (Rep ℤ Gal(L.val/ℚ)) := {
    X₁ := originalRelationModule BL
    X₂ := Rep.free ℤ Gal(L.val/ℚ) BL
    X₃ := BL
    f := originalRelationInclusion BL
    g := originalRelationFreeCover BL
    zero := (originalRelationShortComplex BL).zero }
  let C := arithmeticOriginalStageClassRep Ω a ha L
  let η := arithmeticSourceScalarStageRelationTransport Ω a ha P B c r F i L hFL
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
  let hX₁ : Continuous (fun z : Gal(L.val/ℚ) × X.X₁ => X.X₁.ρ z.1 z.2) :=
    continuous_of_discreteTopology
  let hX₂ : Continuous (fun z : Gal(L.val/ℚ) × X.X₂ => X.X₂.ρ z.1 z.2) :=
    continuous_of_discreteTopology
  let hBL : Continuous (fun z : Gal(L.val/ℚ) × BL => BL.ρ z.1 z.2) :=
    continuous_of_discreteTopology
  let hC : Continuous (fun z : Gal(L.val/ℚ) × C => C.ρ z.1 z.2) :=
    continuous_of_discreteTopology
  exact continuousShortComplexCoefficientObstruction_toAlgebraic X
    (originalRelationShortComplex_shortExact BL) C hX₁ hX₂ hBL hC η y

end
end Dubon2026
