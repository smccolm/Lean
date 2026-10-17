import Dubon2026.ArithmeticSourceScalarStageRelationMaps
import Dubon2026.ArithmeticSourceRelationContinuousDiagram
import Dubon2026.OriginalGaloisRestrictionTowerDiagram

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module Submodule.Quotient.module
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Use the original arithmetic union inclusion. -/
local instance sourceEmbeddedDiagramUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Use the actual finite stage inclusion. -/
local instance sourceEmbeddedDiagramFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

variable [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]

/-- Integer scalar multiplication on the original discrete Hom is continuous. -/
local instance sourceEmbeddedDiagramHomContinuousSMul :
    @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
      (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology

/-- The embedded original stage's presentation maps to the source
presentation through its actual field tower and descended relation diagram. -/
def arithmeticSourceEmbeddedStageDiagram
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B))
    (r : ArithmeticSourceClassRelationData Ω a ha P B c)
    (F : OriginalUnramifiedGaloisStage (Ω := Ω) a) (i : r.stage →ₐ[ℚ] F.val)
    (hi : ∀ x : r.stage, (i x : Ω) = (x.val : Ω)) :
    letI : Algebra F.val (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
      (IntermediateField.inclusion (originalUnramifiedGaloisStage_le_union a F)).toAlgebra
    letI : IsScalarTower ℚ F.val (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
      IsScalarTower.of_algHom (IntermediateField.inclusion (originalUnramifiedGaloisStage_le_union a F))
    (Rep.resFunctor (AlgEquiv.restrictNormalHom F.val :
      Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(F.val/ℚ))).mapShortComplex.obj
        (originalRelationShortComplex (arithmeticOriginalStageRestrictedCoefficient Ω a r.stage F i
          (arithmeticSourceClassRelationStageCoefficient Ω a ha P B c r))) ⟶
      arithmeticSourceRelationPresentation Ω a P B := by
  letI : Algebra F.val (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
    (IntermediateField.inclusion (originalUnramifiedGaloisStage_le_union a F)).toAlgebra
  letI : IsScalarTower ℚ F.val (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
    IsScalarTower.of_algHom (IntermediateField.inclusion (originalUnramifiedGaloisStage_le_union a F))
  letI : Algebra r.stage F.val := i.toAlgebra
  letI : Module r.stage F.val := i.toAlgebra.toModule
  letI : SMul r.stage F.val := i.toAlgebra.toSMul
  letI : IsScalarTower ℚ r.stage F.val := IsScalarTower.of_algHom i
  letI : IsScalarTower r.stage F.val (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
    IsScalarTower.of_algebraMap_eq' (by ext x; exact (hi x).symm)
  let U := originalUnramifiedGaloisUnion (Ω := Ω) a
  let BN := arithmeticSourceClassRelationStageCoefficient Ω a ha P B c r
  exact originalGaloisRelationTowerMap ℚ r.stage F.val U BN ≫
    arithmeticSourceRelationFiniteDiagram Ω a ha P B c r

end
end Dubon2026
