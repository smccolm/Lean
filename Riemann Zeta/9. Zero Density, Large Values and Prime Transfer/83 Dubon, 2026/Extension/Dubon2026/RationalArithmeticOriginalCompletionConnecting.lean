import Dubon2026.RationalArithmeticOriginalCompletionDualDiagram
import Dubon2026.GaloisTowerLocalUnitDualConnecting
import Dubon2026.ContinuousInvariantConnectingRestrictedNaturality

/-! The original completion comparison preserves the actual local dual
connecting class. Both exact sequences and all continuity inputs are
derived, for DUB-17's finite-correction to source-local comparison. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
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



variable (a : 𝓞 ℚ)
  (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (p : ℕ) (hp : p.Prime)

variable (B : Rep.{0} ℤ Gal(F/ℚ))


variable [Finite B] (q : ℕ) [Fact q.Prime] (hCoeff : ∀ b : B, q • b = 0)

/-- The exact completion comparison for the original local dual connecting class. -/
abbrev RationalArithmeticOriginalCompletionConnectingCompatibility : Prop :=
    let X := arithmeticPrimeLocalUnitDualSequence a F B p hp
    let L := galoisTowerLocalRelationComplex ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
      ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F) (rationalPrimeLocalClosure p hp)
      Gal(F/ℚ) (originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
        (rationalArithmeticOriginalPrime a p hp F)) B
    let D := Rep.ofAlgebraAutOnUnits ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
      (rationalPrimeLocalClosure p hp)
    let Y := originalContravariantHomShortComplex L D
    let j := (rationalOriginalCompletionGaloisEquiv p hp).symm.toMonoidHom
    let hj := rationalOriginalCompletionGaloisEquiv_symm_continuous p hp
    let d := rationalArithmeticOriginalCompletionDualDiagram a F p hp B
    letI : Module.Finite ℤ B := Module.Finite.of_finite
    letI : Module.Finite ℤ (Rep.free ℤ Gal(F/ℚ) B) := by
      change Module.Finite ℤ (B →₀ Gal(F/ℚ) →₀ ℤ)
      infer_instance
    letI : TopologicalSpace X.X₁ := ⊥
    letI : DiscreteTopology X.X₁ := ⟨rfl⟩
    letI : TopologicalSpace X.X₂ := ⊥
    letI : DiscreteTopology X.X₂ := ⟨rfl⟩
    letI : TopologicalSpace Y.X₁ := ⊥
    letI : DiscreteTopology Y.X₁ := ⟨rfl⟩
    letI : TopologicalSpace Y.X₂ := ⊥
    letI : DiscreteTopology Y.X₂ := ⟨rfl⟩
    letI : @ContinuousSMul ℤ X.X₁ (X.X₁).hV2.toSMul inferInstance inferInstance :=
      @ContinuousSMul.mk ℤ X.X₁ (X.X₁).hV2.toSMul _ _ continuous_of_discreteTopology
    letI : @ContinuousSMul ℤ Y.X₁ (Y.X₁).hV2.toSMul inferInstance inferInstance :=
      @ContinuousSMul.mk ℤ Y.X₁ (Y.X₁).hV2.toSMul _ _ continuous_of_discreteTopology
    let hX1 := @arithmeticPrimeRestrictedUnitHomAction_continuous a F B p hp inferInstance ⊥ ⟨rfl⟩
    let hX2 := @arithmeticPrimeRestrictedUnitHomAction_continuous a F (Rep.free ℤ Gal(F/ℚ) B) p hp
      inferInstance ⊥ ⟨rfl⟩
    let hY1 := galoisTowerLocalCoefficientUnitHomAction_continuous ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
      ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F) (rationalPrimeLocalClosure p hp)
      Gal(F/ℚ) (originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
        (rationalArithmeticOriginalPrime a p hp F)) B
    let hY2 := galoisTowerPartialFreeUnitHomAction_continuous ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
      ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F) (rationalPrimeLocalClosure p hp)
      Gal(F/ℚ) (originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
        (rationalArithmeticOriginalPrime a p hp F)) B
    let hX := arithmeticPrimeLocalUnitDualSequence_shortExact a F B p hp q hCoeff
    let hY := galoisUnitRelationDualSequence_shortExact
      ((rationalOriginalPrimePlace p hp).adicCompletion ℚ) (rationalPrimeLocalClosure p hp) Gal(F/ℚ)
      ((originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
        (rationalArithmeticOriginalPrime a p hp F)).comp
        (AlgEquiv.restrictNormalHom ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F))) q B hCoeff
    ∀ w : X.X₃.ρ.invariants,
    let wY : Y.X₃.ρ.invariants := ⟨d.τ₃.hom w.val, fun g =>
      (Rep.hom_comm_apply d.τ₃ g w.val).symm.trans (congrArg d.τ₃.hom (w.property (j g)))⟩
    continuousCoefficientH1Map (restrictedCoefficientRep X.X₁ j) Y.X₁
      d.τ₁.hom.toLinearMap continuous_of_discreteTopology (Rep.hom_comm_apply d.τ₁)
      (restrictedCoefficientAction_continuous X.X₁ j hj hX1) hY1
      (continuousRepresentationH1Restriction X.X₁ hX1 j hj
        (continuousShortComplexInvariantConnectingMap X hX hX1 hX2 w)) =
      continuousShortComplexInvariantConnectingMap Y hY hY1 hY2 wY

/-- The actual group and coefficient maps preserve the original local
dual connecting class, with no exactness, diagram or continuity premise. -/
theorem rationalArithmeticOriginalCompletion_connecting :
    RationalArithmeticOriginalCompletionConnectingCompatibility a F p hp B q hCoeff := by
  let X := arithmeticPrimeLocalUnitDualSequence a F B p hp
  let L := galoisTowerLocalRelationComplex ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
    ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F) (rationalPrimeLocalClosure p hp)
    Gal(F/ℚ) (originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
      (rationalArithmeticOriginalPrime a p hp F)) B
  let D := Rep.ofAlgebraAutOnUnits ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
    (rationalPrimeLocalClosure p hp)
  let Y := originalContravariantHomShortComplex L D
  let j := (rationalOriginalCompletionGaloisEquiv p hp).symm.toMonoidHom
  let hj := rationalOriginalCompletionGaloisEquiv_symm_continuous p hp
  let d := rationalArithmeticOriginalCompletionDualDiagram a F p hp B
  letI : Module.Finite ℤ B := Module.Finite.of_finite
  letI : Module.Finite ℤ (Rep.free ℤ Gal(F/ℚ) B) := by
    change Module.Finite ℤ (B →₀ Gal(F/ℚ) →₀ ℤ)
    infer_instance
  letI : TopologicalSpace X.X₁ := ⊥
  letI : DiscreteTopology X.X₁ := ⟨rfl⟩
  letI : TopologicalSpace X.X₂ := ⊥
  letI : DiscreteTopology X.X₂ := ⟨rfl⟩
  letI : TopologicalSpace Y.X₁ := ⊥
  letI : DiscreteTopology Y.X₁ := ⟨rfl⟩
  letI : TopologicalSpace Y.X₂ := ⊥
  letI : DiscreteTopology Y.X₂ := ⟨rfl⟩
  letI : @ContinuousSMul ℤ X.X₁ (X.X₁).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ X.X₁ (X.X₁).hV2.toSMul _ _ continuous_of_discreteTopology
  letI : @ContinuousSMul ℤ Y.X₁ (Y.X₁).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ Y.X₁ (Y.X₁).hV2.toSMul _ _ continuous_of_discreteTopology
  let hX1 := @arithmeticPrimeRestrictedUnitHomAction_continuous a F B p hp inferInstance ⊥ ⟨rfl⟩
  let hX2 := @arithmeticPrimeRestrictedUnitHomAction_continuous a F (Rep.free ℤ Gal(F/ℚ) B) p hp
    inferInstance ⊥ ⟨rfl⟩
  let hY1 := galoisTowerLocalCoefficientUnitHomAction_continuous ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
    ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F) (rationalPrimeLocalClosure p hp)
    Gal(F/ℚ) (originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
      (rationalArithmeticOriginalPrime a p hp F)) B
  let hY2 := galoisTowerPartialFreeUnitHomAction_continuous ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
    ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F) (rationalPrimeLocalClosure p hp)
    Gal(F/ℚ) (originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
      (rationalArithmeticOriginalPrime a p hp F)) B
  let hX := arithmeticPrimeLocalUnitDualSequence_shortExact a F B p hp q hCoeff
  let hY := galoisUnitRelationDualSequence_shortExact
    ((rationalOriginalPrimePlace p hp).adicCompletion ℚ) (rationalPrimeLocalClosure p hp) Gal(F/ℚ)
    ((originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
      (rationalArithmeticOriginalPrime a p hp F)).comp
      (AlgEquiv.restrictNormalHom ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F))) q B hCoeff
  change ∀ w : X.X₃.ρ.invariants, _
  intro w
  exact continuousInvariantConnecting_restricted_naturality X hX hX1 hX2 j hj Y hY hY1 hY2
    d continuous_of_discreteTopology w

end
end Dubon2026
