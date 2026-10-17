import Dubon2026.ArithmeticSourceScalarStageDiagram
import Dubon2026.ArithmeticSourceScalarStageRelationValues

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module Submodule.Quotient.module
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Use the original arithmetic union inclusion. -/
local instance sourceScalarSquareUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Use the actual finite stage inclusion. -/
local instance sourceScalarSquareFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

variable [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]

/-- Integer scalar multiplication on the original discrete Hom is continuous. -/
local instance sourceScalarSquareHomContinuousSMul :
    @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
      (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology

omit [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)] in
/-- The actual enlarged scalar-stage relation satisfies the coefficient
square with the same original source-cocycle relation. This is derived
from the literal class-colimit values, not supplied as a certificate. -/
theorem arithmeticSourceScalarStageDiagram_square
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
    let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(L.val/ℚ) :=
      AlgEquiv.restrictNormalHom L.val
    (Rep.resFunctor π).map (arithmeticSourceScalarStageRelationTransport Ω a ha P B c r F i L hFL) ≫
      arithmeticOriginalStageClassToColimit Ω a ha L =
      (arithmeticSourceScalarStageDiagram Ω a ha P B c r F i L hFL hi).τ₁ ≫ r.relation := by
  letI : Algebra L.val (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
    (IntermediateField.inclusion (originalUnramifiedGaloisStage_le_union a L)).toAlgebra
  letI : IsScalarTower ℚ L.val (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
    IsScalarTower.of_algHom (IntermediateField.inclusion (originalUnramifiedGaloisStage_le_union a L))
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro z
  exact arithmeticSourceScalarStageRelation_colimit Ω a ha P B c r F i L hFL hi z

end
end Dubon2026
