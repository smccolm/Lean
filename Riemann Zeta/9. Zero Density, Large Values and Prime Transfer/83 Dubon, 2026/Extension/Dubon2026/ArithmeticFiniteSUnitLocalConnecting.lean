import Dubon2026.ArithmeticFiniteSUnitDualConnecting
import Dubon2026.ArithmeticPrimeRestrictedUnitHomContinuity
import Dubon2026.ContinuousInvariantConnectingRestrictedNaturality
import Dubon2026.RationalTraceFiniteTowerAction

/-! Localize the actual continuous global class of a finite S-unit
relation. The original arithmetic map, its commuting dual diagram, both
dual exact sequences and all action continuity are derived. This supplies
the connecting-class comparison in DUB-17's prescribed local recovery. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV1 Rep.hV2
attribute [local instance] arithmeticUnitMapAlgebra rationalArithmeticOriginalFiniteGalois
  arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  rationalTraceCompletionArithmeticGalois

local instance arithmeticLocalConnectingAlgebraicClosure : IsAlgClosure ℚ (AlgebraicClosure ℚ) := by
  have hAlg : @AlgebraicClosure.instAlgebra ℚ _ ℚ _ (Algebra.id ℚ) =
      (inferInstance : Algebra ℚ (AlgebraicClosure ℚ)) := Subsingleton.elim _ _
  have h := AlgebraicClosure.instIsAlgClosure ℚ
  rw [hAlg] at h
  exact h

variable (a : 𝓞 ℚ) (ha : a ≠ 0) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
  (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (B : Rep.{0} ℤ Gal(F/ℚ)) [Finite B] (hCoeff : ∀ b : B, q • b = 0)
  (p : ℕ) (hp : p.Prime)

/-- The exact local connecting identity for the actual finite S-unit class. -/
abbrev ArithmeticFiniteSUnitLocalConnectingCompatibility : Prop :=
    let π : rationalArithmeticGaloisGroup a →* Gal(F/ℚ) := AlgEquiv.restrictNormalHom F;
    let j := (rationalPrimeArithmeticRestriction a p hp).toMonoidHom;
    let hj := (rationalPrimeArithmeticRestriction a p hp).continuous;
    let X : ShortComplex (Rep ℤ (rationalArithmeticGaloisGroup a)) := {
      X₁ := Rep.res π (originalRelationModule B)
      X₂ := Rep.res π (Rep.free ℤ Gal(F/ℚ) B)
      X₃ := Rep.res π B
      f := (Rep.resFunctor π).map (originalRelationInclusion B)
      g := (Rep.resFunctor π).map (originalRelationFreeCover B)
      zero := ((originalRelationShortComplex B).map (Rep.resFunctor π)).zero };
    let XP : ShortComplex (Rep ℤ Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp)) := {
      X₁ := Rep.res (π.comp j) (originalRelationModule B)
      X₂ := Rep.res (π.comp j) (Rep.free ℤ Gal(F/ℚ) B)
      X₃ := Rep.res (π.comp j) B
      f := (Rep.resFunctor (π.comp j)).map (originalRelationInclusion B)
      g := (Rep.resFunctor (π.comp j)).map (originalRelationFreeCover B)
      zero := ((originalRelationShortComplex B).map (Rep.resFunctor (π.comp j))).zero };
    let D := originalArithmeticSUnitRepresentation ℚ (AlgebraicClosure ℚ) a ha;
    let E := Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp);
    let Y := originalContravariantHomShortComplex X D;
    let Z := originalContravariantHomShortComplex XP E;
    let d := arithmeticFiniteSUnitLocalDualDiagram a ha F B p hp;
    letI : Finite X.X₃ := inferInstanceAs (Finite B);
    letI : Module.Finite ℤ B := Module.Finite.of_finite;
    letI : Module.Finite ℤ (Rep.free ℤ Gal(F/ℚ) B) := by
      change Module.Finite ℤ (B →₀ Gal(F/ℚ) →₀ ℤ)
      infer_instance;
    letI : TopologicalSpace X.X₁ := ⊥;
    letI : DiscreteTopology X.X₁ := ⟨rfl⟩;
    letI : TopologicalSpace X.X₂ := ⊥;
    letI : DiscreteTopology X.X₂ := ⟨rfl⟩;
    letI : TopologicalSpace X.X₃ := ⊥;
    letI : DiscreteTopology X.X₃ := ⟨rfl⟩;
    letI : TopologicalSpace D := ⊥;
    letI : DiscreteTopology D := ⟨rfl⟩;
    letI : TopologicalSpace E := ⊥;
    letI : DiscreteTopology E := ⟨rfl⟩;
    letI : TopologicalSpace Y.X₁ := ⊥;
    letI : DiscreteTopology Y.X₁ := ⟨rfl⟩;
    letI : TopologicalSpace Y.X₂ := ⊥;
    letI : DiscreteTopology Y.X₂ := ⟨rfl⟩;
    letI : TopologicalSpace Y.X₃ := ⊥;
    letI : DiscreteTopology Y.X₃ := ⟨rfl⟩;
    letI : TopologicalSpace Z.X₁ := ⊥;
    letI : DiscreteTopology Z.X₁ := ⟨rfl⟩;
    letI : TopologicalSpace Z.X₂ := ⊥;
    letI : DiscreteTopology Z.X₂ := ⟨rfl⟩;
    letI : TopologicalSpace Z.X₃ := ⊥;
    letI : DiscreteTopology Z.X₃ := ⟨rfl⟩;
    letI : @ContinuousSMul ℤ X.X₁ (X.X₁).hV2.toSMul inferInstance inferInstance :=
      @ContinuousSMul.mk ℤ X.X₁ (X.X₁).hV2.toSMul _ _ continuous_of_discreteTopology;
    letI : @ContinuousSMul ℤ X.X₂ (X.X₂).hV2.toSMul inferInstance inferInstance :=
      @ContinuousSMul.mk ℤ X.X₂ (X.X₂).hV2.toSMul _ _ continuous_of_discreteTopology;
    letI : @ContinuousSMul ℤ X.X₃ (X.X₃).hV2.toSMul inferInstance inferInstance :=
      @ContinuousSMul.mk ℤ X.X₃ (X.X₃).hV2.toSMul _ _ continuous_of_discreteTopology;
    letI : @ContinuousSMul ℤ D (D).hV2.toSMul inferInstance inferInstance :=
      @ContinuousSMul.mk ℤ D (D).hV2.toSMul _ _ continuous_of_discreteTopology;
    letI : @ContinuousSMul ℤ E (E).hV2.toSMul inferInstance inferInstance :=
      @ContinuousSMul.mk ℤ E (E).hV2.toSMul _ _ continuous_of_discreteTopology;
    letI : @ContinuousSMul ℤ Y.X₁ (Y.X₁).hV2.toSMul inferInstance inferInstance :=
      @ContinuousSMul.mk ℤ Y.X₁ (Y.X₁).hV2.toSMul _ _ continuous_of_discreteTopology;
    letI : @ContinuousSMul ℤ Z.X₁ (Z.X₁).hV2.toSMul inferInstance inferInstance :=
      @ContinuousSMul.mk ℤ Z.X₁ (Z.X₁).hV2.toSMul _ _ continuous_of_discreteTopology;
    let hC := arithmeticFiniteStageRepresentationAction_continuous ℚ (AlgebraicClosure ℚ) a F B;
    let hD := originalArithmeticSUnitAction_continuous ℚ (AlgebraicClosure ℚ) a ha;
    let hU := originalInternalHomAction_continuous_of_finite X.X₃ D hC hD;
    let hW := arithmeticPrimeRestrictedUnitHomAction_continuous a F B p hp;
    let hT := arithmeticPrimeRestrictedUnitHomAction_continuous a F (Rep.free ℤ Gal(F/ℚ) B) p hp;
    let hZ := arithmeticFiniteSUnitLocalDualSequence_shortExact a F B p hp q hCoeff;
    ∀ η : originalRelationModule B ⟶ arithmeticSUnitFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha F,
    let w := arithmeticFiniteSUnitRelationInvariant ℚ (AlgebraicClosure ℚ) a ha F B η
    let wZ : Z.X₃.ρ.invariants := ⟨d.τ₃.hom w.val, fun g =>
      (Rep.hom_comm_apply d.τ₃ g w.val).symm.trans (congrArg d.τ₃.hom (w.property (j g)))⟩
    continuousCoefficientH1Map (restrictedCoefficientRep Y.X₁ j) Z.X₁
      d.τ₁.hom.toLinearMap continuous_of_discreteTopology (Rep.hom_comm_apply d.τ₁)
      (restrictedCoefficientAction_continuous Y.X₁ j hj hU) hW
      (continuousRepresentationH1Restriction Y.X₁ hU j hj
        (arithmeticFiniteSUnitDualConnectingClass ℚ (AlgebraicClosure ℚ) a ha q hqa F B hCoeff η)) =
      continuousShortComplexInvariantConnectingMap Z hZ hW hT wZ

/-- Localizing the constructed global finite S-unit dual class gives
the connecting class of the same locally mapped relation invariant.
Neither dual exactness nor action continuity is supplied as a premise. -/
theorem arithmeticFiniteSUnitDualConnectingClass_local :
    ArithmeticFiniteSUnitLocalConnectingCompatibility a ha q hqa F B hCoeff p hp := by
  let π : rationalArithmeticGaloisGroup a →* Gal(F/ℚ) := AlgEquiv.restrictNormalHom F
  let j := (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
  let hj := (rationalPrimeArithmeticRestriction a p hp).continuous
  let X : ShortComplex (Rep ℤ (rationalArithmeticGaloisGroup a)) := {
    X₁ := Rep.res π (originalRelationModule B)
    X₂ := Rep.res π (Rep.free ℤ Gal(F/ℚ) B)
    X₃ := Rep.res π B
    f := (Rep.resFunctor π).map (originalRelationInclusion B)
    g := (Rep.resFunctor π).map (originalRelationFreeCover B)
    zero := ((originalRelationShortComplex B).map (Rep.resFunctor π)).zero }
  let XP : ShortComplex (Rep ℤ Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp)) := {
    X₁ := Rep.res (π.comp j) (originalRelationModule B)
    X₂ := Rep.res (π.comp j) (Rep.free ℤ Gal(F/ℚ) B)
    X₃ := Rep.res (π.comp j) B
    f := (Rep.resFunctor (π.comp j)).map (originalRelationInclusion B)
    g := (Rep.resFunctor (π.comp j)).map (originalRelationFreeCover B)
    zero := ((originalRelationShortComplex B).map (Rep.resFunctor (π.comp j))).zero }
  let D := originalArithmeticSUnitRepresentation ℚ (AlgebraicClosure ℚ) a ha
  let E := Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)
  let Y := originalContravariantHomShortComplex X D
  let Z := originalContravariantHomShortComplex XP E
  let d := arithmeticFiniteSUnitLocalDualDiagram a ha F B p hp
  letI : Finite X.X₃ := inferInstanceAs (Finite B)
  letI : Module.Finite ℤ B := Module.Finite.of_finite
  letI : Module.Finite ℤ (Rep.free ℤ Gal(F/ℚ) B) := by
    change Module.Finite ℤ (B →₀ Gal(F/ℚ) →₀ ℤ)
    infer_instance
  letI : TopologicalSpace X.X₁ := ⊥
  letI : DiscreteTopology X.X₁ := ⟨rfl⟩
  letI : TopologicalSpace X.X₂ := ⊥
  letI : DiscreteTopology X.X₂ := ⟨rfl⟩
  letI : TopologicalSpace X.X₃ := ⊥
  letI : DiscreteTopology X.X₃ := ⟨rfl⟩
  letI : TopologicalSpace D := ⊥
  letI : DiscreteTopology D := ⟨rfl⟩
  letI : TopologicalSpace E := ⊥
  letI : DiscreteTopology E := ⟨rfl⟩
  letI : TopologicalSpace Y.X₁ := ⊥
  letI : DiscreteTopology Y.X₁ := ⟨rfl⟩
  letI : TopologicalSpace Y.X₂ := ⊥
  letI : DiscreteTopology Y.X₂ := ⟨rfl⟩
  letI : TopologicalSpace Y.X₃ := ⊥
  letI : DiscreteTopology Y.X₃ := ⟨rfl⟩
  letI : TopologicalSpace Z.X₁ := ⊥
  letI : DiscreteTopology Z.X₁ := ⟨rfl⟩
  letI : TopologicalSpace Z.X₂ := ⊥
  letI : DiscreteTopology Z.X₂ := ⟨rfl⟩
  letI : TopologicalSpace Z.X₃ := ⊥
  letI : DiscreteTopology Z.X₃ := ⟨rfl⟩
  letI : @ContinuousSMul ℤ X.X₁ (X.X₁).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ X.X₁ (X.X₁).hV2.toSMul _ _ continuous_of_discreteTopology
  letI : @ContinuousSMul ℤ X.X₂ (X.X₂).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ X.X₂ (X.X₂).hV2.toSMul _ _ continuous_of_discreteTopology
  letI : @ContinuousSMul ℤ X.X₃ (X.X₃).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ X.X₃ (X.X₃).hV2.toSMul _ _ continuous_of_discreteTopology
  letI : @ContinuousSMul ℤ D (D).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ D (D).hV2.toSMul _ _ continuous_of_discreteTopology
  letI : @ContinuousSMul ℤ E (E).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ E (E).hV2.toSMul _ _ continuous_of_discreteTopology
  letI : @ContinuousSMul ℤ Y.X₁ (Y.X₁).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ Y.X₁ (Y.X₁).hV2.toSMul _ _ continuous_of_discreteTopology
  letI : @ContinuousSMul ℤ Z.X₁ (Z.X₁).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ Z.X₁ (Z.X₁).hV2.toSMul _ _ continuous_of_discreteTopology
  let hC := arithmeticFiniteStageRepresentationAction_continuous ℚ (AlgebraicClosure ℚ) a F B
  let hD := originalArithmeticSUnitAction_continuous ℚ (AlgebraicClosure ℚ) a ha
  let hU := originalInternalHomAction_continuous_of_finite X.X₃ D hC hD
  let hV : Continuous (fun z : rationalArithmeticGaloisGroup a × Y.X₂ => Y.X₂.ρ z.1 z.2) := by
    letI : TopologicalSpace (arithmeticRelationFreeSUnitDual ℚ (AlgebraicClosure ℚ) a ha F B) := ⊥
    letI : DiscreteTopology (arithmeticRelationFreeSUnitDual ℚ (AlgebraicClosure ℚ) a ha F B) := ⟨rfl⟩
    exact arithmeticRelationFreeSUnitDualAction_continuous ℚ (AlgebraicClosure ℚ) a ha F B
  let hW := arithmeticPrimeRestrictedUnitHomAction_continuous a F B p hp
  let hT := arithmeticPrimeRestrictedUnitHomAction_continuous a F (Rep.free ℤ Gal(F/ℚ) B) p hp
  let hY := arithmeticRelationSUnitDualSequence_shortExact ℚ (AlgebraicClosure ℚ) a ha q hqa F B hCoeff
  let hZ := arithmeticFiniteSUnitLocalDualSequence_shortExact a F B p hp q hCoeff
  change ∀ η : originalRelationModule B ⟶ arithmeticSUnitFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha F, _
  intro η
  exact continuousInvariantConnecting_restricted_naturality Y hY hU hV j hj Z hZ hW hT
    d continuous_of_discreteTopology
    (arithmeticFiniteSUnitRelationInvariant ℚ (AlgebraicClosure ℚ) a ha F B η)

end
end Dubon2026
