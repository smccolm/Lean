import Dubon2026.ArithmeticSourceRelationContinuousFiniteMaps
import Dubon2026.ContinuousDiscreteH1Surjection

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module Submodule.Quotient.module
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Use the original arithmetic union inclusion. -/
local instance sourceStageH1ComparisonUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Use the actual finite stage inclusion. -/
local instance sourceStageH1ComparisonFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

variable [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]

/-- Integer scalar multiplication on the original discrete Hom is continuous. -/
local instance sourceStageH1ComparisonHomContinuousSMul :
    @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
      (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology

/-- The finite continuous H1 input retains its literal original cocycle class. -/
def arithmeticSourceRelationStageH1ToAlgebraic
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B))
    (r : ArithmeticSourceClassRelationData Ω a ha P B c)
    (y : arithmeticSourceRelationStageContinuousH1 Ω a ha P B c r) :
    groupCohomology (arithmeticSourceClassRelationStageCoefficient Ω a ha P B c r) 1 := by
  let BN := arithmeticSourceClassRelationStageCoefficient Ω a ha P B c r
  letI : TopologicalSpace BN := ⊥
  letI : DiscreteTopology BN := ⟨rfl⟩
  letI : @ContinuousSMul ℤ BN (BN).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ BN (BN).hV2.toSMul _ _ continuous_of_discreteTopology
  exact continuousH1ToAlgebraic BN continuous_of_discreteTopology y

omit [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)] in
/-- Every original finite algebraic H1 input is retained by the actual
continuous input used in the source relation cup comparison. -/
theorem arithmeticSourceRelationStageH1ToAlgebraic_surjective
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B))
    (r : ArithmeticSourceClassRelationData Ω a ha P B c) :
    Function.Surjective (arithmeticSourceRelationStageH1ToAlgebraic Ω a ha P B c r) := by
  let BN := arithmeticSourceClassRelationStageCoefficient Ω a ha P B c r
  letI : TopologicalSpace BN := ⊥
  letI : DiscreteTopology BN := ⟨rfl⟩
  letI : @ContinuousSMul ℤ BN (BN).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ BN (BN).hV2.toSMul _ _ continuous_of_discreteTopology
  exact continuousH1ToAlgebraic_surjective BN continuous_of_discreteTopology

end
end Dubon2026
