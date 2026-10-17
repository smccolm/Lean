import Dubon2026.ArithmeticSourceIdeleRelationMaps

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Retain the original arithmetic union's rational inclusion. -/
local instance sourceIdeleContinuousCupUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Retain the original finite Galois stage's rational inclusion. -/
local instance sourceIdeleContinuousCupFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

variable
  [TopologicalSpace (arithmeticSPlaceColimitRep ℚ Ω a ha)] [DiscreteTopology (arithmeticSPlaceColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)] [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B)] [DiscreteTopology (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B)]

/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticSourceIdeleContinuousCupLocalInstance1 : @ContinuousSMul ℤ (arithmeticSPlaceColimitRep ℚ Ω a ha) (arithmeticSPlaceColimitRep ℚ Ω a ha).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticSPlaceColimitRep ℚ Ω a ha) (arithmeticSPlaceColimitRep ℚ Ω a ha).hV2.toSMul _ _ continuous_of_discreteTopology
/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticSourceIdeleContinuousCupLocalInstance2 : @ContinuousSMul ℤ (arithmeticClassesModOutsideColimitRep ℚ Ω a ha) (arithmeticClassesModOutsideColimitRep ℚ Ω a ha).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticClassesModOutsideColimitRep ℚ Ω a ha) (arithmeticClassesModOutsideColimitRep ℚ Ω a ha).hV2.toSMul _ _ continuous_of_discreteTopology
/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticSourceIdeleContinuousCupLocalInstance3 : @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B) (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B) (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology

/-- Continuous H2 of the actual source-idele coefficient with its proved arithmetic action. -/
abbrev arithmeticSourceIdeleContinuousH2 :=
  ContinuousRepresentationH2 (arithmeticSPlaceColimitRep ℚ Ω a ha) (arithmeticSPlaceColimitAction_continuous ℚ Ω a ha)

/-- Map the actual source-idele cup into the same continuous class H2 used
by the constructed relation obstruction. -/
def arithmeticSourceIdeleContinuousH2ToClasses :
    arithmeticSourceIdeleContinuousH2 Ω a ha →ₗ[ℤ] arithmeticSourceRelationContinuousH2 Ω a ha :=
  continuousCoefficientH2Map (arithmeticSPlaceColimitRep ℚ Ω a ha) (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)
    (arithmeticSourceIdeleToFullClassColimit Ω a ha).hom.toLinearMap continuous_of_discreteTopology
    (Rep.hom_comm_apply (arithmeticSourceIdeleToFullClassColimit Ω a ha))
    (arithmeticSPlaceColimitAction_continuous ℚ Ω a ha)
    (arithmeticClassesModOutsideColimitAction_continuous ℚ Ω a ha)

/-- The actual source-idele evaluation cup for the identical finite
coefficient and continuous H1 input used by the scalar relation. -/
def arithmeticSourceIdeleContinuousCupClass [Finite B]
    (y : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B))
    (x : arithmeticSourceRelationContinuousH1 Ω a P B) :
    arithmeticSourceIdeleContinuousH2 Ω a ha := by
  let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(P/ℚ) :=
    AlgEquiv.restrictNormalHom P
  let A := Rep.res π B
  let J := (arithmeticSPlaceColimitRep ℚ Ω a ha)
  let U := (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B)
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : @ContinuousSMul ℤ A A.hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ A A.hV2.toSMul _ _ continuous_of_discreteTopology
  let hA := arithmeticFiniteStageRepresentationAction_continuous ℚ Ω a P B
  let hJ := arithmeticSPlaceColimitAction_continuous ℚ Ω a ha
  let hU := arithmeticSourceIdeleHomAction_continuous ℚ Ω a ha A hA
  exact continuousH1Cup A U J (originalInternalHomEvaluation A J)
    (originalInternalHomEvaluation_equivariant A J) continuous_of_discreteTopology
    hA hU hJ x ((continuousRepresentationCoboundariesOne U hU).mkQ y)

end
end Dubon2026
