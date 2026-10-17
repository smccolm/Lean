import Dubon2026.ArithmeticSourceRelationContinuousCupMaps

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module Submodule.Quotient.module
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Use the original arithmetic union inclusion. -/
local instance sourceContinuousCupIdentityUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Use the actual finite stage inclusion. -/
local instance sourceContinuousCupIdentityFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

variable [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]

/-- Integer scalar multiplication on the original discrete Hom is continuous. -/
local instance sourceContinuousCupIdentityHomContinuousSMul :
    @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
      (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology

/-- The actual source-cocycle lift identifies its continuous cup with
the original relation connecting class, without class-target Ext exactness. -/
theorem arithmeticSourceClassRelationData_cup_continuous [Finite B]
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B))
    (r : ArithmeticSourceClassRelationData Ω a ha P B c)
    (x : arithmeticSourceRelationContinuousH1 Ω a P B) :
    arithmeticSourceRelationContinuousCupClass Ω a ha P B c x =
      arithmeticSourceRelationContinuousConnectingClass Ω a ha P B r.relation x := by
  let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(P/ℚ) := AlgEquiv.restrictNormalHom P
  let X : ShortComplex (Rep ℤ Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ)) := {
    X₁ := Rep.res π (originalRelationModule B)
    X₂ := Rep.res π (Rep.free ℤ Gal(P/ℚ) B)
    X₃ := Rep.res π B
    f := (Rep.resFunctor π).map (originalRelationInclusion B)
    g := (Rep.resFunctor π).map (originalRelationFreeCover B)
    zero := ((originalRelationShortComplex B).map (Rep.resFunctor π)).zero }
  let D := arithmeticClassesModOutsideColimitRep ℚ Ω a ha
  letI : TopologicalSpace X.X₁ := ⊥
  letI : DiscreteTopology X.X₁ := ⟨rfl⟩
  letI : TopologicalSpace X.X₂ := ⊥
  letI : DiscreteTopology X.X₂ := ⟨rfl⟩
  letI : TopologicalSpace X.X₃ := ⊥
  letI : DiscreteTopology X.X₃ := ⟨rfl⟩
  letI : TopologicalSpace ((Rep.ihom X.X₃).obj D) := ⊥
  letI : DiscreteTopology ((Rep.ihom X.X₃).obj D) := ⟨rfl⟩
  letI : TopologicalSpace ((Rep.ihom X.X₂).obj D) := ⊥
  letI : DiscreteTopology ((Rep.ihom X.X₂).obj D) := ⟨rfl⟩
  letI : TopologicalSpace ((Rep.ihom X.X₁).obj D) := ⊥
  letI : DiscreteTopology ((Rep.ihom X.X₁).obj D) := ⟨rfl⟩
  letI : @ContinuousSMul ℤ X.X₁ (X.X₁).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ X.X₁ (X.X₁).hV2.toSMul _ _ continuous_of_discreteTopology
  letI : @ContinuousSMul ℤ X.X₂ (X.X₂).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ X.X₂ (X.X₂).hV2.toSMul _ _ continuous_of_discreteTopology
  letI : @ContinuousSMul ℤ X.X₃ (X.X₃).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ X.X₃ (X.X₃).hV2.toSMul _ _ continuous_of_discreteTopology
  letI : @ContinuousSMul ℤ D (D).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ D (D).hV2.toSMul _ _ continuous_of_discreteTopology
  letI : @ContinuousSMul ℤ ((Rep.ihom X.X₃).obj D) (((Rep.ihom X.X₃).obj D)).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ ((Rep.ihom X.X₃).obj D) (((Rep.ihom X.X₃).obj D)).hV2.toSMul _ _ continuous_of_discreteTopology
  let hA := arithmeticFiniteStageRepresentationAction_continuous ℚ Ω a P (originalRelationModule B)
  let hB := arithmeticFiniteStageRepresentationAction_continuous ℚ Ω a P (Rep.free ℤ Gal(P/ℚ) B)
  let hC := arithmeticFiniteStageRepresentationAction_continuous ℚ Ω a P B
  let hD := arithmeticClassesModOutsideColimitAction_continuous ℚ Ω a ha
  let hU := originalInternalHomAction_continuous_of_finite X.X₃ D hC hD
  let hX : X.ShortExact := originalRelationGroupChange_shortExact π B
  let f : arithmeticFiniteCoefficientSourceClassHom Ω a ha P B ⟶ (Rep.ihom X.X₃).obj D :=
    arithmeticSourceClassHomComparison ℚ Ω a ha (Rep.res π B)
  let u := continuousCoefficientCocycleOneMap
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B) ((Rep.ihom X.X₃).obj D)
      f.hom.toLinearMap continuous_of_discreteTopology (Rep.hom_comm_apply f) c
  have hV := arithmeticRelationFreeClassHomAction_continuous Ω a ha P B
  exact originalRelationCup_explicit_lift_continuous X D hX hA hB hC hU hV hD
    x u r.lift r.relation r.lift_coboundary r.relation_eq

end
end Dubon2026
