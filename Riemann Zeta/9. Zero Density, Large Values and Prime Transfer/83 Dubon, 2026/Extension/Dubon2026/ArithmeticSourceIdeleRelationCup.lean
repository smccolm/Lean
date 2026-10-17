import Dubon2026.ArithmeticSourceIdeleContinuousCup

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Retain the original arithmetic union's rational inclusion. -/
local instance sourceIdeleRelationCupUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Retain the original finite Galois stage's rational inclusion. -/
local instance sourceIdeleRelationCupFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

variable
  [TopologicalSpace (arithmeticSPlaceColimitRep ℚ Ω a ha)] [DiscreteTopology (arithmeticSPlaceColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)] [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B)] [DiscreteTopology (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B)]

/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticSourceIdeleRelationCupLocalInstance1 : @ContinuousSMul ℤ (arithmeticSPlaceColimitRep ℚ Ω a ha) (arithmeticSPlaceColimitRep ℚ Ω a ha).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticSPlaceColimitRep ℚ Ω a ha) (arithmeticSPlaceColimitRep ℚ Ω a ha).hV2.toSMul _ _ continuous_of_discreteTopology
/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticSourceIdeleRelationCupLocalInstance2 : @ContinuousSMul ℤ (arithmeticClassesModOutsideColimitRep ℚ Ω a ha) (arithmeticClassesModOutsideColimitRep ℚ Ω a ha).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticClassesModOutsideColimitRep ℚ Ω a ha) (arithmeticClassesModOutsideColimitRep ℚ Ω a ha).hV2.toSMul _ _ continuous_of_discreteTopology
/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticSourceIdeleRelationCupLocalInstance3 : @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B) (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B) (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology


variable [TopologicalSpace (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]
/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticSourceIdeleRelationCupLocalInstance4 : @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology

/-- The source-induced relation cup is the image of the actual source-idele
cup under the same full-class-colimit comparison. No compatibility premise
or global injectivity of the continuous-to-algebraic H2 map is supplied. -/
theorem arithmeticSourceIdeleContinuousCupClass_relation [Finite B]
    (y : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B))
    (x : arithmeticSourceRelationContinuousH1 Ω a P B) :
    arithmeticSourceIdeleContinuousH2ToClasses Ω a ha
      (arithmeticSourceIdeleContinuousCupClass Ω a ha P B y x) =
    arithmeticSourceRelationContinuousCupClass Ω a ha P B
      (arithmeticSourceIdeleCocycleQuotient Ω a ha P B y) x := by
  induction x using Submodule.Quotient.induction_on with
  | _ f =>
    apply congrArg (continuousRepresentationCoboundariesTwo
      (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)
      (arithmeticClassesModOutsideColimitAction_continuous ℚ Ω a ha)).mkQ
    apply Subtype.ext
    apply Subtype.ext
    funext gh
    let A := Rep.res (AlgEquiv.restrictNormalHom P :
      Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(P/ℚ)) B
    exact Rep.hom_comm_apply (arithmeticSourceIdeleToFullClassColimit Ω a ha) gh.1
      (originalInternalHomEvaluation A (arithmeticSPlaceColimitRep ℚ Ω a ha)
        (A.ρ gh.1⁻¹ (f.val gh.1)) (y.val gh.2))

end
end Dubon2026
