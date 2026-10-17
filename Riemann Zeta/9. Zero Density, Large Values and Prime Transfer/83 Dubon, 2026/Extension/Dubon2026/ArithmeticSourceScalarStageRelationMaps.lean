import Dubon2026.ArithmeticSourceClassScalarStage
import Dubon2026.ArithmeticOriginalStageClassColimit

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module Submodule.Quotient.module
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Use the original arithmetic union inclusion. -/
local instance sourceScalarRelationMapsUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Use the actual finite stage inclusion. -/
local instance sourceScalarRelationMapsFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

variable [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]

/-- Integer scalar multiplication on the original discrete Hom is continuous. -/
local instance sourceScalarRelationMapsHomContinuousSMul :
    @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
      (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology

/-- The exact coefficient at the original enlarged scalar-criterion stage. -/
abbrev arithmeticSourceScalarStageCoefficient
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B))
    (r : ArithmeticSourceClassRelationData Ω a ha P B c)
    (F : OriginalUnramifiedGaloisStage (Ω := Ω) a) (i : r.stage →ₐ[ℚ] F.val)
    (L : OriginalUnramifiedGaloisStage (Ω := Ω) a)
    (hFL : F.val.toIntermediateField ≤ L.val.toIntermediateField) : Rep.{0} ℤ Gal(L.val/ℚ) := by
  letI : Algebra F.val L.val := (IntermediateField.inclusion hFL).toRingHom.toAlgebra
  letI : IsScalarTower ℚ F.val L.val := IsScalarTower.of_algHom (IntermediateField.inclusion hFL)
  let BF := arithmeticOriginalStageRestrictedCoefficient Ω a r.stage F i
    (arithmeticSourceClassRelationStageCoefficient Ω a ha P B c r)
  exact Rep.res (AlgEquiv.restrictNormalHom F.val : Gal(L.val/ℚ) →* Gal(F.val/ℚ)) BF

/-- The three actual relation-kernel maps from the enlarged scalar stage
back to the same original source presentation, on their literal values. -/
def arithmeticSourceScalarStageToSourceRelation
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B))
    (r : ArithmeticSourceClassRelationData Ω a ha P B c)
    (F : OriginalUnramifiedGaloisStage (Ω := Ω) a) (i : r.stage →ₐ[ℚ] F.val)
    (L : OriginalUnramifiedGaloisStage (Ω := Ω) a)
    (hFL : F.val.toIntermediateField ≤ L.val.toIntermediateField) :
    originalRelationModule (arithmeticSourceScalarStageCoefficient Ω a ha P B c r F i L hFL) →ₗ[ℤ]
      (arithmeticSourceRelationPresentation Ω a P B).X₁ := by
  letI : Algebra P r.stage := (IntermediateField.inclusion r.le_stage).toAlgebra
  letI : Module P r.stage := (IntermediateField.inclusion r.le_stage).toAlgebra.toModule
  letI : SMul P r.stage := (IntermediateField.inclusion r.le_stage).toAlgebra.toSMul
  letI : IsScalarTower ℚ P r.stage := IsScalarTower.of_algHom (IntermediateField.inclusion r.le_stage)
  letI : IsScalarTower P r.stage (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra r.stage F.val := i.toAlgebra
  letI : Module r.stage F.val := i.toAlgebra.toModule
  letI : SMul r.stage F.val := i.toAlgebra.toSMul
  letI : IsScalarTower ℚ r.stage F.val := IsScalarTower.of_algHom i
  letI : Algebra F.val L.val := (IntermediateField.inclusion hFL).toRingHom.toAlgebra
  letI : IsScalarTower ℚ F.val L.val := IsScalarTower.of_algHom (IntermediateField.inclusion hFL)
  let BN := arithmeticSourceClassRelationStageCoefficient Ω a ha P B c r
  let BF := arithmeticOriginalStageRestrictedCoefficient Ω a r.stage F i BN
  let π : Gal(r.stage/ℚ) →* Gal(P/ℚ) := AlgEquiv.restrictNormalHom P
  let τ : Gal(F.val/ℚ) →* Gal(r.stage/ℚ) := AlgEquiv.restrictNormalHom r.stage
  let υ : Gal(L.val/ℚ) →* Gal(F.val/ℚ) := AlgEquiv.restrictNormalHom F.val
  exact (originalRelationGroupChange π B).hom.toLinearMap.comp
    ((originalRelationGroupChange τ BN).hom.toLinearMap.comp
      (originalRelationGroupChange υ BF).hom.toLinearMap)

/-- The same finite relation transported through the embedded and
enlarged original stages, retaining the original exceptional-class maps. -/
def arithmeticSourceScalarStageRelationTransport
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B))
    (r : ArithmeticSourceClassRelationData Ω a ha P B c)
    (F : OriginalUnramifiedGaloisStage (Ω := Ω) a) (i : r.stage →ₐ[ℚ] F.val)
    (L : OriginalUnramifiedGaloisStage (Ω := Ω) a)
    (hFL : F.val.toIntermediateField ≤ L.val.toIntermediateField) :
    originalRelationModule (arithmeticSourceScalarStageCoefficient Ω a ha P B c r F i L hFL) ⟶
      arithmeticOriginalStageClassRep Ω a ha L := by
  letI : Algebra F.val L.val := (IntermediateField.inclusion hFL).toRingHom.toAlgebra
  letI : IsScalarTower ℚ F.val L.val := IsScalarTower.of_algHom (IntermediateField.inclusion hFL)
  exact arithmeticOriginalEnlargedRelationClassTransport Ω a ha r.stage F i
    (arithmeticSourceClassRelationStageCoefficient Ω a ha P B c r) L hFL
    (arithmeticSourceClassRelationStageHom Ω a ha P B c r)

end
end Dubon2026
