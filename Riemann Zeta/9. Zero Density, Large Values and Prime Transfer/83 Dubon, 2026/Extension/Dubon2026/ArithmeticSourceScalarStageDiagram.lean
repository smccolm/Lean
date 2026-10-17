import Dubon2026.ArithmeticSourceScalarStageRelationMaps
import Dubon2026.ArithmeticSourceRelationContinuousDiagram
import Dubon2026.ArithmeticSourceEmbeddedStageDiagram

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module Submodule.Quotient.module
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Use the original arithmetic union inclusion. -/
local instance sourceScalarDiagramUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Use the actual finite stage inclusion. -/
local instance sourceScalarDiagramFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

variable [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]

/-- Integer scalar multiplication on the original discrete Hom is continuous. -/
local instance sourceScalarDiagramHomContinuousSMul :
    @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
      (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology

/-- The exact scalar-stage relation presentation maps to the original
source presentation through the two actual field towers and the descended
relation diagram. The field-value premise comes from the proved placement. -/
def arithmeticSourceScalarStageDiagram
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B))
    (r : ArithmeticSourceClassRelationData Ω a ha P B c)
    (F : OriginalUnramifiedGaloisStage (Ω := Ω) a) (i : r.stage →ₐ[ℚ] F.val)
    (L : OriginalUnramifiedGaloisStage (Ω := Ω) a)
    (hFL : F.val.toIntermediateField ≤ L.val.toIntermediateField)
    (hi : ∀ x : r.stage, (i x : Ω) = (x.val : Ω)) :
    letI : Algebra L.val (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
      (IntermediateField.inclusion (originalUnramifiedGaloisStage_le_union a L)).toAlgebra
    letI : IsScalarTower ℚ L.val (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
      IsScalarTower.of_algHom (IntermediateField.inclusion (originalUnramifiedGaloisStage_le_union a L))
    (Rep.resFunctor (AlgEquiv.restrictNormalHom L.val :
      Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(L.val/ℚ))).mapShortComplex.obj
        (originalRelationShortComplex (arithmeticSourceScalarStageCoefficient Ω a ha P B c r F i L hFL)) ⟶
      arithmeticSourceRelationPresentation Ω a P B := by
  letI : Algebra L.val (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
    (IntermediateField.inclusion (originalUnramifiedGaloisStage_le_union a L)).toAlgebra
  letI : IsScalarTower ℚ L.val (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
    IsScalarTower.of_algHom (IntermediateField.inclusion (originalUnramifiedGaloisStage_le_union a L))
  letI : Algebra F.val (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
    (IntermediateField.inclusion (originalUnramifiedGaloisStage_le_union a F)).toAlgebra
  letI : IsScalarTower ℚ F.val (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
    IsScalarTower.of_algHom (IntermediateField.inclusion (originalUnramifiedGaloisStage_le_union a F))
  letI : Algebra F.val L.val := (IntermediateField.inclusion hFL).toRingHom.toAlgebra
  letI : IsScalarTower ℚ F.val L.val := IsScalarTower.of_algHom (IntermediateField.inclusion hFL)
  letI : IsScalarTower F.val L.val (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let U := originalUnramifiedGaloisUnion (Ω := Ω) a
  let BF := arithmeticOriginalStageRestrictedCoefficient Ω a r.stage F i
    (arithmeticSourceClassRelationStageCoefficient Ω a ha P B c r)
  exact originalGaloisRelationTowerMap ℚ F.val L.val U BF ≫
    arithmeticSourceEmbeddedStageDiagram Ω a ha P B c r F i hi

omit [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)] in
/-- The constructed scalar-stage diagram has exactly the three canonical
relation-kernel maps on coefficient values. -/
theorem arithmeticSourceScalarStageDiagram_relation_apply
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B))
    (r : ArithmeticSourceClassRelationData Ω a ha P B c)
    (F : OriginalUnramifiedGaloisStage (Ω := Ω) a) (i : r.stage →ₐ[ℚ] F.val)
    (L : OriginalUnramifiedGaloisStage (Ω := Ω) a)
    (hFL : F.val.toIntermediateField ≤ L.val.toIntermediateField)
    (hi : ∀ x : r.stage, (i x : Ω) = (x.val : Ω))
    (z : originalRelationModule (arithmeticSourceScalarStageCoefficient Ω a ha P B c r F i L hFL)) :
    (arithmeticSourceScalarStageDiagram Ω a ha P B c r F i L hFL hi).τ₁.hom z =
      arithmeticSourceScalarStageToSourceRelation Ω a ha P B c r F i L hFL z := rfl

end
end Dubon2026
