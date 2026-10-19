import Dubon2026.ArithmeticFiniteSUnitCorrectionGlobal
import Dubon2026.ArithmeticRelationSUnitCupAdjunction
import Mathlib.RepresentationTheory.Invariants

/-! Construct the continuous global S-unit-dual H1 class of the actual
finite relation morphism, using the native proved dual exact sequence.
The same invariant gives its global cup identity. This is the class input
to DUB-17 local recovery; prescribed local restrictions remain unproved. -/
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

/-- The invariant internal-Hom element of the actual finite S-unit relation. -/
def arithmeticFiniteSUnitRelationInvariant
    (η : originalRelationModule B ⟶ arithmeticSUnitFiniteStageRep K Ω a ha F) :
    let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(F/K) :=
      AlgEquiv.restrictNormalHom F
    ((Rep.ihom (Rep.res π (originalRelationModule B))).obj
      (originalArithmeticSUnitRepresentation K Ω a ha)).ρ.invariants :=
  (Representation.linHom.invariantsEquivRepHom _ _).symm
    (arithmeticFiniteSUnitRelationToGlobal K Ω a ha F B η)

/-- The actual continuous global dual class of the finite S-unit relation. -/
def arithmeticFiniteSUnitDualConnectingClass :
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
    ∀ _ : originalRelationModule B ⟶ arithmeticSUnitFiniteStageRep K Ω a ha F,
      ContinuousRepresentationH1 ((Rep.ihom X.X₃).obj D) hU := by
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
  let hC := arithmeticFiniteStageRepresentationAction_continuous K Ω a F B
  let hD := originalArithmeticSUnitAction_continuous K Ω a ha
  let hU := originalInternalHomAction_continuous_of_finite X.X₃ D hC hD
  let hV := arithmeticRelationFreeSUnitDualAction_continuous K Ω a ha F B
  let hY : (originalContravariantHomShortComplex X D).ShortExact := arithmeticRelationSUnitDualSequence_shortExact K Ω a ha q hqa F B hCoeff
  change ∀ η : originalRelationModule B ⟶ arithmeticSUnitFiniteStageRep K Ω a ha F,
    ContinuousRepresentationH1 ((Rep.ihom X.X₃).obj D) hU
  intro η
  exact continuousShortComplexInvariantConnectingMap
    (originalContravariantHomShortComplex X D) hY hU hV
    (arithmeticFiniteSUnitRelationInvariant K Ω a ha F B η)

/-- Every global coefficient H1 cup with the constructed class is the
relation cup of the same finite S-unit morphism. -/
theorem arithmeticFiniteSUnitDualConnectingClass_cup :
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
    let hX : X.ShortExact := originalRelationGroupChange_shortExact π B;
    ∀ η : originalRelationModule B ⟶ arithmeticSUnitFiniteStageRep K Ω a ha F,
    let w := arithmeticFiniteSUnitRelationInvariant K Ω a ha F B η
    ∀ x : ContinuousRepresentationH1 X.X₃ hC,
    continuousInvariantRightH2Map X.X₁ ((Rep.ihom X.X₁).obj D) D
      (originalInternalHomEvaluation X.X₁ D)
      (originalInternalHomEvaluation_equivariant X.X₁ D)
      continuous_of_discreteTopology hA hD w
      (continuousShortComplexConnectingMap X hX hA hB hC x) =
    continuousH1Cup X.X₃ ((Rep.ihom X.X₃).obj D) D
      (originalInternalHomEvaluation X.X₃ D)
      (originalInternalHomEvaluation_equivariant X.X₃ D)
      continuous_of_discreteTopology hC hU hD x
      (arithmeticFiniteSUnitDualConnectingClass K Ω a ha q hqa F B hCoeff η) := by
  exact fun η x => arithmeticRelationSUnitCup_adjunction K Ω a ha q hqa F B hCoeff x
    (arithmeticFiniteSUnitRelationInvariant K Ω a ha F B η)

end
end Dubon2026
