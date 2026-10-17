import Dubon2026.ContinuousInternalHomCupPostcomposition
import Dubon2026.ArithmeticSourceHomContinuity

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Preserve the original arithmetic union's rational inclusion. -/
local instance sourceIdeleCupUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (A : Rep.{0} ℤ Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ))
  [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (hA : Continuous (fun z : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) × A => A.ρ z.1 z.2))
  [TopologicalSpace (arithmeticSPlaceColimitRep ℚ Ω a ha)] [DiscreteTopology (arithmeticSPlaceColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticSPlaceClassColimitRep ℚ Ω a ha)] [DiscreteTopology (arithmeticSPlaceClassColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticSourceIdeleHomRep ℚ Ω a ha A)] [DiscreteTopology (arithmeticSourceIdeleHomRep ℚ Ω a ha A)]
  [TopologicalSpace (arithmeticSourceClassHomRep ℚ Ω a ha A)] [DiscreteTopology (arithmeticSourceClassHomRep ℚ Ω a ha A)]

/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticSourceIdeleCupImageLocalInstance1 : @ContinuousSMul ℤ A A.hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ A A.hV2.toSMul _ _ continuous_of_discreteTopology
/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticSourceIdeleCupImageLocalInstance2 : @ContinuousSMul ℤ (arithmeticSPlaceColimitRep ℚ Ω a ha) (arithmeticSPlaceColimitRep ℚ Ω a ha).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticSPlaceColimitRep ℚ Ω a ha) (arithmeticSPlaceColimitRep ℚ Ω a ha).hV2.toSMul _ _ continuous_of_discreteTopology
/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticSourceIdeleCupImageLocalInstance3 : @ContinuousSMul ℤ (arithmeticSPlaceClassColimitRep ℚ Ω a ha) (arithmeticSPlaceClassColimitRep ℚ Ω a ha).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticSPlaceClassColimitRep ℚ Ω a ha) (arithmeticSPlaceClassColimitRep ℚ Ω a ha).hV2.toSMul _ _ continuous_of_discreteTopology
/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticSourceIdeleCupImageLocalInstance4 : @ContinuousSMul ℤ (arithmeticSourceIdeleHomRep ℚ Ω a ha A) (arithmeticSourceIdeleHomRep ℚ Ω a ha A).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticSourceIdeleHomRep ℚ Ω a ha A) (arithmeticSourceIdeleHomRep ℚ Ω a ha A).hV2.toSMul _ _ continuous_of_discreteTopology
/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticSourceIdeleCupImageLocalInstance5 : @ContinuousSMul ℤ (arithmeticSourceClassHomRep ℚ Ω a ha A) (arithmeticSourceClassHomRep ℚ Ω a ha A).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticSourceClassHomRep ℚ Ω a ha A) (arithmeticSourceClassHomRep ℚ Ω a ha A).hV2.toSMul _ _ continuous_of_discreteTopology

/-- The actual source-idele Hom class maps to the original source-class
evaluation cup through the same source quotient. All target and Hom action
continuity follows from the proved arithmetic actions and finite source. -/
theorem arithmeticSourceIdeleH1Cup_quotient
    (x : ContinuousRepresentationH1 A hA)
    (y : ContinuousRepresentationH1 (arithmeticSourceIdeleHomRep ℚ Ω a ha A) (arithmeticSourceIdeleHomAction_continuous ℚ Ω a ha A hA)) :
    continuousCoefficientH2Map (arithmeticSPlaceColimitRep ℚ Ω a ha) (arithmeticSPlaceClassColimitRep ℚ Ω a ha) (arithmeticSPlaceColimitQuotientRepHom ℚ Ω a ha).hom.toLinearMap continuous_of_discreteTopology
      (Rep.hom_comm_apply (arithmeticSPlaceColimitQuotientRepHom ℚ Ω a ha)) (arithmeticSPlaceColimitAction_continuous ℚ Ω a ha) (arithmeticSPlaceClassColimitAction_continuous ℚ Ω a ha)
      (continuousH1Cup A (arithmeticSourceIdeleHomRep ℚ Ω a ha A) (arithmeticSPlaceColimitRep ℚ Ω a ha) (originalInternalHomEvaluation A (arithmeticSPlaceColimitRep ℚ Ω a ha))
        (originalInternalHomEvaluation_equivariant A (arithmeticSPlaceColimitRep ℚ Ω a ha)) continuous_of_discreteTopology hA (arithmeticSourceIdeleHomAction_continuous ℚ Ω a ha A hA) (arithmeticSPlaceColimitAction_continuous ℚ Ω a ha) x y) =
    continuousH1Cup A (arithmeticSourceClassHomRep ℚ Ω a ha A) (arithmeticSPlaceClassColimitRep ℚ Ω a ha) (originalInternalHomEvaluation A (arithmeticSPlaceClassColimitRep ℚ Ω a ha))
      (originalInternalHomEvaluation_equivariant A (arithmeticSPlaceClassColimitRep ℚ Ω a ha)) continuous_of_discreteTopology hA (arithmeticSourceClassHomAction_continuous ℚ Ω a ha A hA) (arithmeticSPlaceClassColimitAction_continuous ℚ Ω a ha) x
      (continuousCoefficientH1Map (arithmeticSourceIdeleHomRep ℚ Ω a ha A) (arithmeticSourceClassHomRep ℚ Ω a ha A)
        ((Rep.ihom A).map (arithmeticSPlaceColimitQuotientRepHom ℚ Ω a ha)).hom.toLinearMap continuous_of_discreteTopology
        (Rep.hom_comm_apply ((Rep.ihom A).map (arithmeticSPlaceColimitQuotientRepHom ℚ Ω a ha))) (arithmeticSourceIdeleHomAction_continuous ℚ Ω a ha A hA) (arithmeticSourceClassHomAction_continuous ℚ Ω a ha A hA) y) := by
  exact @continuousInternalHomH1Cup_postcomposition _ _ _ _ A (arithmeticSPlaceColimitRep ℚ Ω a ha) (arithmeticSPlaceClassColimitRep ℚ Ω a ha) _ _ _ _ _ _
    (inferInstanceAs (TopologicalSpace (arithmeticSourceIdeleHomRep ℚ Ω a ha A)))
    (inferInstanceAs (DiscreteTopology (arithmeticSourceIdeleHomRep ℚ Ω a ha A)))
    (inferInstanceAs (TopologicalSpace (arithmeticSourceClassHomRep ℚ Ω a ha A)))
    (inferInstanceAs (DiscreteTopology (arithmeticSourceClassHomRep ℚ Ω a ha A)))
    hA (arithmeticSPlaceColimitAction_continuous ℚ Ω a ha) (arithmeticSPlaceClassColimitAction_continuous ℚ Ω a ha) (arithmeticSourceIdeleHomAction_continuous ℚ Ω a ha A hA) (arithmeticSourceClassHomAction_continuous ℚ Ω a ha A hA) (arithmeticSPlaceColimitQuotientRepHom ℚ Ω a ha) x y

end
end Dubon2026
