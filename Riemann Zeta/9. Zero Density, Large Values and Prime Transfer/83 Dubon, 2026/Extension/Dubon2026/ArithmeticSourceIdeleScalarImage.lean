import Dubon2026.ArithmeticSourceIdeleRelationCup
import Dubon2026.ArithmeticSourceScalarContinuousCup

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Retain the original arithmetic union's rational inclusion. -/
local instance sourceIdeleScalarImageUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Retain the original finite Galois stage's rational inclusion. -/
local instance sourceIdeleScalarImageFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

variable
  [TopologicalSpace (arithmeticSPlaceColimitRep ℚ Ω a ha)] [DiscreteTopology (arithmeticSPlaceColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)] [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B)] [DiscreteTopology (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B)]

/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticSourceIdeleScalarImageLocalInstance1 : @ContinuousSMul ℤ (arithmeticSPlaceColimitRep ℚ Ω a ha) (arithmeticSPlaceColimitRep ℚ Ω a ha).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticSPlaceColimitRep ℚ Ω a ha) (arithmeticSPlaceColimitRep ℚ Ω a ha).hV2.toSMul _ _ continuous_of_discreteTopology
/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticSourceIdeleScalarImageLocalInstance2 : @ContinuousSMul ℤ (arithmeticClassesModOutsideColimitRep ℚ Ω a ha) (arithmeticClassesModOutsideColimitRep ℚ Ω a ha).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticClassesModOutsideColimitRep ℚ Ω a ha) (arithmeticClassesModOutsideColimitRep ℚ Ω a ha).hV2.toSMul _ _ continuous_of_discreteTopology
/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticSourceIdeleScalarImageLocalInstance3 : @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B) (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B) (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology


variable [TopologicalSpace (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]
/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticSourceIdeleScalarImageLocalInstance4 : @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology


/-- At the identical enlarged scalar stage, the actual obstruction image
is the class image of the original source-idele cup. -/
theorem arithmeticSourceIdeleCup_scalar_obstruction_image [Finite B]
    (z : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B)) :
    let c := arithmeticSourceIdeleCocycleQuotient Ω a ha P B z
    ∀ (r : ArithmeticSourceClassRelationData Ω a ha P B c)
      (F : OriginalUnramifiedGaloisStage (Ω := Ω) a) (i : r.stage →ₐ[ℚ] F.val)
      (L : OriginalUnramifiedGaloisStage (Ω := Ω) a)
      (hFL : F.val.toIntermediateField ≤ L.val.toIntermediateField)
      (hi : ∀ x : r.stage, (i x : Ω) = (x.val : Ω))
      (y : arithmeticSourceScalarStageContinuousH1 Ω a ha P B c r F i L hFL),
      arithmeticSourceIdeleContinuousH2ToClasses Ω a ha
        (arithmeticSourceIdeleContinuousCupClass Ω a ha P B z
          (arithmeticSourceScalarContinuousH1Inflation Ω a ha P B c r F i L hFL hi y)) =
        arithmeticSourceScalarContinuousObstruction Ω a ha P B c r F i L hFL y := by
  intro c r F i L hFL hi y
  exact (arithmeticSourceIdeleContinuousCupClass_relation Ω a ha P B z
    (arithmeticSourceScalarContinuousH1Inflation Ω a ha P B c r F i L hFL hi y)).trans
      (arithmeticSourceClassRelationData_scalar_continuous_cup Ω a ha P B c r F i L hFL hi y)

/-- An actual source-idele cocycle constructs its relation data and retains
the idele image identity at every embedded and enlarged scalar stage. -/
theorem arithmeticSourceIdeleCocycle_exists_scalar_obstruction_image [Finite B]
    (z : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B)) :
    let c := arithmeticSourceIdeleCocycleQuotient Ω a ha P B z
    ∃ r : ArithmeticSourceClassRelationData Ω a ha P B c,
      ∀ (F : OriginalUnramifiedGaloisStage (Ω := Ω) a) (i : r.stage →ₐ[ℚ] F.val)
      (L : OriginalUnramifiedGaloisStage (Ω := Ω) a)
      (hFL : F.val.toIntermediateField ≤ L.val.toIntermediateField)
      (hi : ∀ x : r.stage, (i x : Ω) = (x.val : Ω))
      (y : arithmeticSourceScalarStageContinuousH1 Ω a ha P B c r F i L hFL),
      arithmeticSourceIdeleContinuousH2ToClasses Ω a ha
        (arithmeticSourceIdeleContinuousCupClass Ω a ha P B z
          (arithmeticSourceScalarContinuousH1Inflation Ω a ha P B c r F i L hFL hi y)) =
        arithmeticSourceScalarContinuousObstruction Ω a ha P B c r F i L hFL y := by
  intro c
  let r := Classical.choice (arithmeticSourceClassRelationData_nonempty Ω a ha P B c)
  exact ⟨r, arithmeticSourceIdeleCup_scalar_obstruction_image Ω a ha P B z r⟩

end
end Dubon2026
