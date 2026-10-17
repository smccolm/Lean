import Dubon2026.OriginalDualRelationCupAdjunction
import Dubon2026.ArithmeticRelationDualSequence
import Dubon2026.ArithmeticRelationFreeHomContinuity
import Dubon2026.ArithmeticFiniteStageActionContinuity
import Dubon2026.OriginalInternalHomActionContinuity

/-! # The actual arithmetic S-unit dual relation cup identity

The original relation presentation is restricted along the literal finite
Galois-stage map. Its S-unit dual is exact by the proved integer Ext
vanishing. All coefficient actions and evaluation maps are constructed.
This supplies the relation-to-continuous-cup comparison on DUB-17's
reverse localization dependency chain. The group retains its Krull topology.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  [IsAlgClosure K Ω] (a : 𝓞 K) (ha : a ≠ 0)
  (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 K) ∣ a)
  (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
  (B : Rep.{0} ℤ Gal(F/K)) [Finite B] (hCoeff : ∀ b : B, q • b = 0)

/-- The actual restricted relation sequence and its proved S-unit dual
give this cup identity with every action and exactness premise discharged. -/
theorem arithmeticRelationSUnitCup_adjunction :
    let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(F/K) := AlgEquiv.restrictNormalHom F;
    let X : ShortComplex (Rep ℤ Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K)) := {
      X₁ := Rep.res π (originalRelationModule B)
      X₂ := Rep.res π (Rep.free ℤ Gal(F/K) B)
      X₃ := Rep.res π B
      f := (Rep.resFunctor π).map (originalRelationInclusion B)
      g := (Rep.resFunctor π).map (originalRelationFreeCover B)
      zero := ((originalRelationShortComplex B).map (Rep.resFunctor π)).zero };
    let D := originalArithmeticSUnitRepresentation K Ω a ha;
    letI : TopologicalSpace X.X₁ := ⊥;
    letI : DiscreteTopology X.X₁ := ⟨rfl⟩;
    letI : TopologicalSpace X.X₂ := ⊥;
    letI : DiscreteTopology X.X₂ := ⟨rfl⟩;
    letI : TopologicalSpace X.X₃ := ⊥;
    letI : DiscreteTopology X.X₃ := ⟨rfl⟩;
    letI : TopologicalSpace D := ⊥;
    letI : DiscreteTopology D := ⟨rfl⟩;
    letI : TopologicalSpace ((Rep.ihom X.X₃).obj D) := ⊥;
    letI : DiscreteTopology ((Rep.ihom X.X₃).obj D) := ⟨rfl⟩;
    letI : TopologicalSpace ((Rep.ihom X.X₂).obj D) := ⊥;
    letI : DiscreteTopology ((Rep.ihom X.X₂).obj D) := ⟨rfl⟩;
    letI : TopologicalSpace ((Rep.ihom X.X₁).obj D) := ⊥;
    letI : DiscreteTopology ((Rep.ihom X.X₁).obj D) := ⟨rfl⟩;
    letI : @ContinuousSMul ℤ X.X₁ (X.X₁).hV2.toSMul inferInstance inferInstance :=
      @ContinuousSMul.mk ℤ X.X₁ (X.X₁).hV2.toSMul _ _ continuous_of_discreteTopology;
    letI : @ContinuousSMul ℤ X.X₂ (X.X₂).hV2.toSMul inferInstance inferInstance :=
      @ContinuousSMul.mk ℤ X.X₂ (X.X₂).hV2.toSMul _ _ continuous_of_discreteTopology;
    letI : @ContinuousSMul ℤ X.X₃ (X.X₃).hV2.toSMul inferInstance inferInstance :=
      @ContinuousSMul.mk ℤ X.X₃ (X.X₃).hV2.toSMul _ _ continuous_of_discreteTopology;
    letI : @ContinuousSMul ℤ D (D).hV2.toSMul inferInstance inferInstance :=
      @ContinuousSMul.mk ℤ D (D).hV2.toSMul _ _ continuous_of_discreteTopology;
    letI : @ContinuousSMul ℤ ((Rep.ihom X.X₃).obj D) (((Rep.ihom X.X₃).obj D)).hV2.toSMul inferInstance inferInstance :=
      @ContinuousSMul.mk ℤ ((Rep.ihom X.X₃).obj D) (((Rep.ihom X.X₃).obj D)).hV2.toSMul _ _ continuous_of_discreteTopology;
    let hA := arithmeticFiniteStageRepresentationAction_continuous K Ω a F (originalRelationModule B);
    let hB := arithmeticFiniteStageRepresentationAction_continuous K Ω a F (Rep.free ℤ Gal(F/K) B);
    let hC := arithmeticFiniteStageRepresentationAction_continuous K Ω a F B;
    let hD := originalArithmeticSUnitAction_continuous K Ω a ha;
    let hU := originalInternalHomAction_continuous_of_finite X.X₃ D hC hD;
    let hV := arithmeticRelationFreeSUnitDualAction_continuous K Ω a ha F B;
    let hX : X.ShortExact := originalRelationGroupChange_shortExact π B;
    let hY : (originalContravariantHomShortComplex X D).ShortExact := arithmeticRelationSUnitDualSequence_shortExact K Ω a ha q hqa F B hCoeff;
    ∀ (x : ContinuousRepresentationH1 X.X₃ hC)
    (w : ((Rep.ihom X.X₁).obj D).ρ.invariants),
    continuousInvariantRightH2Map X.X₁ ((Rep.ihom X.X₁).obj D) D
      (originalInternalHomEvaluation X.X₁ D)
      (originalInternalHomEvaluation_equivariant X.X₁ D)
      continuous_of_discreteTopology hA hD w
      (continuousShortComplexConnectingMap X hX hA hB hC x) =
    continuousH1Cup X.X₃ ((Rep.ihom X.X₃).obj D) D
      (originalInternalHomEvaluation X.X₃ D)
      (originalInternalHomEvaluation_equivariant X.X₃ D)
      continuous_of_discreteTopology hC hU hD x
      (continuousShortComplexInvariantConnectingMap
        (originalContravariantHomShortComplex X D) hY hU hV w) := by
  let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(F/K) := AlgEquiv.restrictNormalHom F
  let X : ShortComplex (Rep ℤ Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K)) := {
    X₁ := Rep.res π (originalRelationModule B)
    X₂ := Rep.res π (Rep.free ℤ Gal(F/K) B)
    X₃ := Rep.res π B
    f := (Rep.resFunctor π).map (originalRelationInclusion B)
    g := (Rep.resFunctor π).map (originalRelationFreeCover B)
    zero := ((originalRelationShortComplex B).map (Rep.resFunctor π)).zero }
  let D := originalArithmeticSUnitRepresentation K Ω a ha
  letI : TopologicalSpace X.X₁ := ⊥
  letI : DiscreteTopology X.X₁ := ⟨rfl⟩
  letI : TopologicalSpace X.X₂ := ⊥
  letI : DiscreteTopology X.X₂ := ⟨rfl⟩
  letI : TopologicalSpace X.X₃ := ⊥
  letI : DiscreteTopology X.X₃ := ⟨rfl⟩
  letI : TopologicalSpace D := ⊥
  letI : DiscreteTopology D := ⟨rfl⟩
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
  let hA := arithmeticFiniteStageRepresentationAction_continuous K Ω a F (originalRelationModule B)
  let hB := arithmeticFiniteStageRepresentationAction_continuous K Ω a F (Rep.free ℤ Gal(F/K) B)
  let hC := arithmeticFiniteStageRepresentationAction_continuous K Ω a F B
  let hD := originalArithmeticSUnitAction_continuous K Ω a ha
  let hU := originalInternalHomAction_continuous_of_finite X.X₃ D hC hD
  let hV := arithmeticRelationFreeSUnitDualAction_continuous K Ω a ha F B
  let hX : X.ShortExact := originalRelationGroupChange_shortExact π B
  let hY : (originalContravariantHomShortComplex X D).ShortExact := arithmeticRelationSUnitDualSequence_shortExact K Ω a ha q hqa F B hCoeff
  change ∀ (x : ContinuousRepresentationH1 X.X₃ hC)
    (w : ((Rep.ihom X.X₁).obj D).ρ.invariants),
    continuousInvariantRightH2Map X.X₁ ((Rep.ihom X.X₁).obj D) D
      (originalInternalHomEvaluation X.X₁ D)
      (originalInternalHomEvaluation_equivariant X.X₁ D)
      continuous_of_discreteTopology hA hD w
      (continuousShortComplexConnectingMap X hX hA hB hC x) =
    continuousH1Cup X.X₃ ((Rep.ihom X.X₃).obj D) D
      (originalInternalHomEvaluation X.X₃ D)
      (originalInternalHomEvaluation_equivariant X.X₃ D)
      continuous_of_discreteTopology hC hU hD x
      (continuousShortComplexInvariantConnectingMap
        (originalContravariantHomShortComplex X D) hY hU hV w)
  intro x w
  exact originalDualRelationCup_adjunction X D hX hY hA hB hC hU hV hD x w

/-- The actual restricted relation sequence and its proved S-unit dual
give this cup identity with every action and exactness premise discharged. -/
theorem arithmeticRelationSUnitCup_toAlgebraic :
    let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(F/K) := AlgEquiv.restrictNormalHom F;
    let X : ShortComplex (Rep ℤ Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K)) := {
      X₁ := Rep.res π (originalRelationModule B)
      X₂ := Rep.res π (Rep.free ℤ Gal(F/K) B)
      X₃ := Rep.res π B
      f := (Rep.resFunctor π).map (originalRelationInclusion B)
      g := (Rep.resFunctor π).map (originalRelationFreeCover B)
      zero := ((originalRelationShortComplex B).map (Rep.resFunctor π)).zero };
    let D := originalArithmeticSUnitRepresentation K Ω a ha;
    letI : TopologicalSpace X.X₁ := ⊥;
    letI : DiscreteTopology X.X₁ := ⟨rfl⟩;
    letI : TopologicalSpace X.X₂ := ⊥;
    letI : DiscreteTopology X.X₂ := ⟨rfl⟩;
    letI : TopologicalSpace X.X₃ := ⊥;
    letI : DiscreteTopology X.X₃ := ⟨rfl⟩;
    letI : TopologicalSpace D := ⊥;
    letI : DiscreteTopology D := ⟨rfl⟩;
    letI : TopologicalSpace ((Rep.ihom X.X₃).obj D) := ⊥;
    letI : DiscreteTopology ((Rep.ihom X.X₃).obj D) := ⟨rfl⟩;
    letI : TopologicalSpace ((Rep.ihom X.X₂).obj D) := ⊥;
    letI : DiscreteTopology ((Rep.ihom X.X₂).obj D) := ⟨rfl⟩;
    letI : TopologicalSpace ((Rep.ihom X.X₁).obj D) := ⊥;
    letI : DiscreteTopology ((Rep.ihom X.X₁).obj D) := ⟨rfl⟩;
    letI : @ContinuousSMul ℤ X.X₁ (X.X₁).hV2.toSMul inferInstance inferInstance :=
      @ContinuousSMul.mk ℤ X.X₁ (X.X₁).hV2.toSMul _ _ continuous_of_discreteTopology;
    letI : @ContinuousSMul ℤ X.X₂ (X.X₂).hV2.toSMul inferInstance inferInstance :=
      @ContinuousSMul.mk ℤ X.X₂ (X.X₂).hV2.toSMul _ _ continuous_of_discreteTopology;
    letI : @ContinuousSMul ℤ X.X₃ (X.X₃).hV2.toSMul inferInstance inferInstance :=
      @ContinuousSMul.mk ℤ X.X₃ (X.X₃).hV2.toSMul _ _ continuous_of_discreteTopology;
    letI : @ContinuousSMul ℤ D (D).hV2.toSMul inferInstance inferInstance :=
      @ContinuousSMul.mk ℤ D (D).hV2.toSMul _ _ continuous_of_discreteTopology;
    letI : @ContinuousSMul ℤ ((Rep.ihom X.X₃).obj D) (((Rep.ihom X.X₃).obj D)).hV2.toSMul inferInstance inferInstance :=
      @ContinuousSMul.mk ℤ ((Rep.ihom X.X₃).obj D) (((Rep.ihom X.X₃).obj D)).hV2.toSMul _ _ continuous_of_discreteTopology;
    let hC := arithmeticFiniteStageRepresentationAction_continuous K Ω a F B;
    let hD := originalArithmeticSUnitAction_continuous K Ω a ha;
    let hU := originalInternalHomAction_continuous_of_finite X.X₃ D hC hD;
    let hV := arithmeticRelationFreeSUnitDualAction_continuous K Ω a ha F B;
    let hX : X.ShortExact := originalRelationGroupChange_shortExact π B;
    let hY : (originalContravariantHomShortComplex X D).ShortExact := arithmeticRelationSUnitDualSequence_shortExact K Ω a ha q hqa F B hCoeff;
    ∀ (x : ContinuousRepresentationH1 X.X₃ hC)
    (w : ((Rep.ihom X.X₁).obj D).ρ.invariants),
    continuousH2ToAlgebraic D hD
      (continuousH1Cup X.X₃ ((Rep.ihom X.X₃).obj D) D
        (originalInternalHomEvaluation X.X₃ D)
        (originalInternalHomEvaluation_equivariant X.X₃ D)
        continuous_of_discreteTopology hC hU hD x
        (continuousShortComplexInvariantConnectingMap
          (originalContravariantHomShortComplex X D) hY hU hV w)) =
    groupCohomology.map (MonoidHom.id Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K)) (originalInvariantHomMorphism X.X₁ D w) 2
      (groupCohomology.δ hX 1 2 rfl (continuousH1ToAlgebraic X.X₃ hC x)) := by
  let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(F/K) := AlgEquiv.restrictNormalHom F
  let X : ShortComplex (Rep ℤ Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K)) := {
    X₁ := Rep.res π (originalRelationModule B)
    X₂ := Rep.res π (Rep.free ℤ Gal(F/K) B)
    X₃ := Rep.res π B
    f := (Rep.resFunctor π).map (originalRelationInclusion B)
    g := (Rep.resFunctor π).map (originalRelationFreeCover B)
    zero := ((originalRelationShortComplex B).map (Rep.resFunctor π)).zero }
  let D := originalArithmeticSUnitRepresentation K Ω a ha
  letI : TopologicalSpace X.X₁ := ⊥
  letI : DiscreteTopology X.X₁ := ⟨rfl⟩
  letI : TopologicalSpace X.X₂ := ⊥
  letI : DiscreteTopology X.X₂ := ⟨rfl⟩
  letI : TopologicalSpace X.X₃ := ⊥
  letI : DiscreteTopology X.X₃ := ⟨rfl⟩
  letI : TopologicalSpace D := ⊥
  letI : DiscreteTopology D := ⟨rfl⟩
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
  let hA := arithmeticFiniteStageRepresentationAction_continuous K Ω a F (originalRelationModule B)
  let hB := arithmeticFiniteStageRepresentationAction_continuous K Ω a F (Rep.free ℤ Gal(F/K) B)
  let hC := arithmeticFiniteStageRepresentationAction_continuous K Ω a F B
  let hD := originalArithmeticSUnitAction_continuous K Ω a ha
  let hU := originalInternalHomAction_continuous_of_finite X.X₃ D hC hD
  let hV := arithmeticRelationFreeSUnitDualAction_continuous K Ω a ha F B
  let hX : X.ShortExact := originalRelationGroupChange_shortExact π B
  let hY : (originalContravariantHomShortComplex X D).ShortExact := arithmeticRelationSUnitDualSequence_shortExact K Ω a ha q hqa F B hCoeff
  change ∀ (x : ContinuousRepresentationH1 X.X₃ hC)
    (w : ((Rep.ihom X.X₁).obj D).ρ.invariants),
    continuousH2ToAlgebraic D hD
      (continuousH1Cup X.X₃ ((Rep.ihom X.X₃).obj D) D
        (originalInternalHomEvaluation X.X₃ D)
        (originalInternalHomEvaluation_equivariant X.X₃ D)
        continuous_of_discreteTopology hC hU hD x
        (continuousShortComplexInvariantConnectingMap
          (originalContravariantHomShortComplex X D) hY hU hV w)) =
    groupCohomology.map (MonoidHom.id Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K)) (originalInvariantHomMorphism X.X₁ D w) 2
      (groupCohomology.δ hX 1 2 rfl (continuousH1ToAlgebraic X.X₃ hC x))
  intro x w
  exact originalDualRelationCup_toAlgebraic X D hX hY hA hB hC hU hV hD x w

end
end Dubon2026
