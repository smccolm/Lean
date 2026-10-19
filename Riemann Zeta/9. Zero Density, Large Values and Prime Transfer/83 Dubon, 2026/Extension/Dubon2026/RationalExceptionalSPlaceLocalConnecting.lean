import Dubon2026.RationalExceptionalSPlaceLocalRelation
import Dubon2026.RationalArithmeticOriginalCompletionConnecting

/-! The actual assembled exceptional S-place relation gives exactly the
source-local dual connecting class after completion comparison. This
composes the checked invariant evaluation and connecting square for
DUB-17's prescribed local-class recovery. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance]
  localRelationCupCoefficientHomTopology localRelationCupCoefficientHomDiscrete
  localRelationCupCoefficientHomContinuousSMul localRelationCupFreeHomTopology
  localRelationCupFreeHomDiscrete localRelationCupFreeHomContinuousSMul

private theorem localDualConnecting_eq_of_invariant
    (K L Ω : Type) [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
    [IsGalois K L] [IsGalois K Ω] [FiniteDimensional K L] [IsAlgClosed Ω]
    (H : Type) [Group H] [Finite H] (ι : Gal(L/K) →* H) (B : Rep.{0} ℤ H) [Finite B]
    (q : ℕ) [Fact q.Prime] (hCoeff : ∀ b : B, q • b = 0)
    (ψ : Rep.res ι (originalRelationModule B) ⟶ Rep.ofAlgebraAutOnUnits K L)
    (w : ((Rep.ihom (galoisTowerLocalRelationComplex K L Ω H ι B).X₁).obj
      (Rep.ofAlgebraAutOnUnits K Ω)).ρ.invariants)
    (hw : w.val = (galoisTowerLocalUnitRelationInvariant K L Ω H ι B ψ).val) :
    continuousShortComplexInvariantConnectingMap
      (originalContravariantHomShortComplex (galoisTowerLocalRelationComplex K L Ω H ι B)
        (Rep.ofAlgebraAutOnUnits K Ω))
      (galoisUnitRelationDualSequence_shortExact K Ω H
        (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))) q B hCoeff)
      (galoisTowerLocalCoefficientUnitHomAction_continuous K L Ω H ι B)
      (galoisTowerPartialFreeUnitHomAction_continuous K L Ω H ι B) w =
      galoisTowerLocalUnitDualConnectingClass K L Ω H ι B q hCoeff ψ := by
  exact congrArg
    (continuousShortComplexInvariantConnectingMap
      (originalContravariantHomShortComplex (galoisTowerLocalRelationComplex K L Ω H ι B)
        (Rep.ofAlgebraAutOnUnits K Ω))
      (galoisUnitRelationDualSequence_shortExact K Ω H
        (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))) q B hCoeff)
      (galoisTowerLocalCoefficientUnitHomAction_continuous K L Ω H ι B)
      (galoisTowerPartialFreeUnitHomAction_continuous K L Ω H ι B)) (Subtype.ext hw)

open scoped NumberField Classical
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV1 Rep.hV2
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitCompletionNumberField arithmeticOrbitCompletionBaseAlgebra
  arithmeticOrbitCompletionValuation arithmeticOrbitCompletionTopology arithmeticOrbitCompletionLocalField
  arithmeticOrbitCompletionValuationExtension arithmeticOrbitCompletionUniformity arithmeticOrbitCompletionUniformAdd
  arithmeticOrbitCompletionTargetAlgebra arithmeticOrbitCompletionClosureAlgebra
  arithmeticOrbitCompletionGlobalAlgebra
  rationalOriginalCompletionTargetAlgebra rationalOriginalCompletionClosureAlgebra
  rationalOriginalCompletionClosureTower rationalOriginalCompletionGalois rationalArithmeticOriginalPrimeLiesOver
  originalAdicRelationCompletionAlgebra originalAdicLocalRelationGalois originalAdicLocalRelationCupFinite
  rationalArithmeticOriginalCompletion_closureTower rationalArithmeticOriginalFiniteGalois
  rationalTraceCompletionArithmeticGalois




attribute [local instance] rationalExceptionalIndexedPrimeLiesOver
variable (a : 𝓞 ℚ) (ha : a ≠ 0)
  (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (B : Rep.{0} ℤ Gal(F/ℚ))
  (ψ : ∀ p : rationalArithmeticExceptionalPrimes a ha,
    Rep.res (originalAdicCompletionGaloisInclusion ℚ F
      (rationalExceptionalIndexedBasePrime a ha p) (rationalExceptionalIndexedUpperPrime a ha F p).val)
      (originalRelationModule B) ⟶
    Rep.ofAlgebraAutOnUnits ((rationalExceptionalIndexedBasePrime a ha p).adicCompletion ℚ)
      ((rationalExceptionalIndexedUpperPrime a ha F p).val.adicCompletion F))


variable [Finite B] (q : ℕ) [Fact q.Prime] (hCoeff : ∀ b : B, q • b = 0)
  (p : rationalArithmeticExceptionalPrimes a ha)

/-- Exact source-local connecting recovery from the original assembled S-place relation. -/
abbrev RationalExceptionalSPlaceLocalConnectingCompatibility : Prop :=
    let X := arithmeticPrimeLocalUnitDualSequence a F B p.val.val p.val.property
    let L := galoisTowerLocalRelationComplex ((rationalOriginalPrimePlace p.val.val p.val.property).adicCompletion ℚ)
      ((rationalArithmeticOriginalPrime a p.val.val p.val.property F).adicCompletion F) (rationalPrimeLocalClosure p.val.val p.val.property)
      Gal(F/ℚ) (originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p.val.val p.val.property)
        (rationalArithmeticOriginalPrime a p.val.val p.val.property F)) B
    let D := Rep.ofAlgebraAutOnUnits ((rationalOriginalPrimePlace p.val.val p.val.property).adicCompletion ℚ)
      (rationalPrimeLocalClosure p.val.val p.val.property)
    let Y := originalContravariantHomShortComplex L D
    let j := (rationalOriginalCompletionGaloisEquiv p.val.val p.val.property).symm.toMonoidHom
    let hj := rationalOriginalCompletionGaloisEquiv_symm_continuous p.val.val p.val.property
    let d := rationalArithmeticOriginalCompletionDualDiagram a F p.val.val p.val.property B
    letI : Module.Finite ℤ B := Module.Finite.of_finite
    letI : TopologicalSpace X.X₁ := ⊥
    letI : DiscreteTopology X.X₁ := ⟨rfl⟩
    letI : TopologicalSpace Y.X₁ := ⊥
    letI : DiscreteTopology Y.X₁ := ⟨rfl⟩
    letI : @ContinuousSMul ℤ X.X₁ (X.X₁).hV2.toSMul inferInstance inferInstance :=
      @ContinuousSMul.mk ℤ X.X₁ (X.X₁).hV2.toSMul _ _ continuous_of_discreteTopology
    letI : @ContinuousSMul ℤ Y.X₁ (Y.X₁).hV2.toSMul inferInstance inferInstance :=
      @ContinuousSMul.mk ℤ Y.X₁ (Y.X₁).hV2.toSMul _ _ continuous_of_discreteTopology
    let hX1 := @arithmeticPrimeRestrictedUnitHomAction_continuous a F B p.val.val p.val.property inferInstance ⊥ ⟨rfl⟩
    let hY1 := galoisTowerLocalCoefficientUnitHomAction_continuous ((rationalOriginalPrimePlace p.val.val p.val.property).adicCompletion ℚ)
      ((rationalArithmeticOriginalPrime a p.val.val p.val.property F).adicCompletion F) (rationalPrimeLocalClosure p.val.val p.val.property)
      Gal(F/ℚ) (originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p.val.val p.val.property)
        (rationalArithmeticOriginalPrime a p.val.val p.val.property F)) B
    let π := (AlgEquiv.restrictNormalHom F : rationalArithmeticGaloisGroup a →* Gal(F/ℚ)).comp
      (rationalPrimeArithmeticRestriction a p.val.val p.val.property).toMonoidHom
    let Φ := rationalExceptionalSPlaceRelation a ha F B ψ
    let φ := (Rep.resFunctor π).map Φ ≫ rationalArithmeticSPlaceLocalMorphism a ha F p
    let w := (Representation.linHom.invariantsEquivRepHom _ _).symm φ
    continuousCoefficientH1Map (restrictedCoefficientRep X.X₁ j) Y.X₁
      d.τ₁.hom.toLinearMap continuous_of_discreteTopology (Rep.hom_comm_apply d.τ₁)
      (restrictedCoefficientAction_continuous X.X₁ j hj hX1) hY1
      (continuousRepresentationH1Restriction X.X₁ hX1 j hj
        (arithmeticPrimeLocalUnitDualConnecting a F B p.val.val p.val.property q hCoeff w)) =
      galoisTowerLocalUnitDualConnectingClass ((rationalExceptionalIndexedBasePrime a ha p).adicCompletion ℚ)
      ((rationalExceptionalIndexedUpperPrime a ha F p).val.adicCompletion F)
      (rationalPrimeLocalClosure p.val.val p.val.property) Gal(F/ℚ)
      (originalAdicCompletionGaloisInclusion ℚ F
        (rationalExceptionalIndexedBasePrime a ha p) (rationalExceptionalIndexedUpperPrime a ha F p).val)
      B q hCoeff (ψ p)

/-- Completion comparison of the assembled S-place relation's local
dual class recovers its original source-local dual class. No family,
exactness, continuity or comparison assumption is supplied. -/
theorem rationalExceptionalSPlaceRelation_local_connecting :
    RationalExceptionalSPlaceLocalConnectingCompatibility a ha F B ψ q hCoeff p := by
  let L := galoisTowerLocalRelationComplex ((rationalOriginalPrimePlace p.val.val p.val.property).adicCompletion ℚ)
    ((rationalArithmeticOriginalPrime a p.val.val p.val.property F).adicCompletion F) (rationalPrimeLocalClosure p.val.val p.val.property)
    Gal(F/ℚ) (originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p.val.val p.val.property)
      (rationalArithmeticOriginalPrime a p.val.val p.val.property F)) B
  let D := Rep.ofAlgebraAutOnUnits ((rationalOriginalPrimePlace p.val.val p.val.property).adicCompletion ℚ)
    (rationalPrimeLocalClosure p.val.val p.val.property)
  let Y := originalContravariantHomShortComplex L D
  let j := (rationalOriginalCompletionGaloisEquiv p.val.val p.val.property).symm.toMonoidHom
  let d := rationalArithmeticOriginalCompletionDualDiagram a F p.val.val p.val.property B
  let π := (AlgEquiv.restrictNormalHom F : rationalArithmeticGaloisGroup a →* Gal(F/ℚ)).comp
    (rationalPrimeArithmeticRestriction a p.val.val p.val.property).toMonoidHom
  let Φ := rationalExceptionalSPlaceRelation a ha F B ψ
  let φ := (Rep.resFunctor π).map Φ ≫ rationalArithmeticSPlaceLocalMorphism a ha F p
  let w := (Representation.linHom.invariantsEquivRepHom _ _).symm φ
  have h := rationalArithmeticOriginalCompletion_connecting a F p.val.val p.val.property B q hCoeff w
  have hw := rationalExceptionalSPlaceRelation_local_invariant a ha F B ψ p
  let wY : Y.X₃.ρ.invariants := ⟨d.τ₃.hom w.val, fun g =>
    (Rep.hom_comm_apply d.τ₃ g w.val).symm.trans (congrArg d.τ₃.hom (w.property (j g)))⟩
  exact h.trans (localDualConnecting_eq_of_invariant ((rationalExceptionalIndexedBasePrime a ha p).adicCompletion ℚ)
      ((rationalExceptionalIndexedUpperPrime a ha F p).val.adicCompletion F)
      (rationalPrimeLocalClosure p.val.val p.val.property) Gal(F/ℚ)
      (originalAdicCompletionGaloisInclusion ℚ F
        (rationalExceptionalIndexedBasePrime a ha p) (rationalExceptionalIndexedUpperPrime a ha F p).val)
      B q hCoeff (ψ p) wY hw)

end
end Dubon2026
