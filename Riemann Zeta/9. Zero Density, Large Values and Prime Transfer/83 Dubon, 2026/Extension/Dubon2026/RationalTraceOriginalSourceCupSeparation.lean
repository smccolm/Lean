import Dubon2026.RationalTraceOriginalMappedCupSeparation

/-! The retained source contract gives cups against every original local
coefficient class. Its tested specializations determine the actual
prime-local classes by the already proved perfect-pairing comparison. -/
namespace Dubon2026
noncomputable section
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

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime]
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
  (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (hker : ∀ u : rationalArithmeticGaloisGroup a,
    AlgEquiv.restrictNormalHom F u = 1 →
    ∀ x : rationalArithmeticTraceZeroIntegerRep a q σ,
      (rationalArithmeticTraceZeroIntegerRep a q σ).ρ u x = x)
  (p : ℕ) (hp : p.Prime)

attribute [local instance] traceOriginalFiniteRepFinite primeTraceIntegerContinuousSMul
  traceOriginalCoefficientTopology traceOriginalCoefficientDiscrete traceOriginalCoefficientContinuousSMul
  traceCartierOriginalHomTopology traceCartierOriginalHomDiscrete
  traceOriginalSourceHomContinuousSMul traceOriginalTargetHomTopology
  traceOriginalTargetHomDiscrete traceOriginalTargetHomContinuousSMul
  localRelationCupCoefficientTopology localRelationCupCoefficientDiscrete
  localRelationCupCoefficientContinuousSMul localRelationCupUnitsTopology
  localRelationCupUnitsDiscrete localRelationCupUnitsContinuousSMul
  originalAdicRelationCupHomTopology originalAdicRelationCupHomDiscrete
  originalAdicRelationCupHomContinuousSMul

variable (hσ : Continuous σ) (hn : (Fintype.card ι : ZMod q) ≠ 0)


/-- Retain the original discrete local roots-of-unity coefficient. -/
local instance sourceCupSeparationRootTopology : TopologicalSpace
    (galoisRootOfUnityRepresentation (K := rationalPrimeLocalField p hp)
      (Ω := rationalPrimeLocalClosure p hp) q) := ⊥
local instance sourceCupSeparationRootDiscrete : DiscreteTopology
    (galoisRootOfUnityRepresentation (K := rationalPrimeLocalField p hp)
      (Ω := rationalPrimeLocalClosure p hp) q) := ⟨rfl⟩


/-- Equality of all actual original source cups identifies the prime-local classes. -/
theorem rationalTraceOriginalMappedHomH1_eq_of_source_cups
    (u v : ContinuousRepresentationH1 (rationalPrimeTraceUnitHomRep p hp q
      (σ.comp (rationalPrimeArithmeticRestriction a p hp)))
      (rationalPrimeTraceUnitHomAction_continuous p hp q
        (σ.comp (rationalPrimeArithmeticRestriction a p hp))
        (hσ.comp (rationalPrimeArithmeticRestriction a p hp).continuous) hn))
    (h : ∀ z : galoisTowerLocalCoefficientH1 ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
      ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F)
      (rationalPrimeLocalClosure p hp) Gal(F/ℚ)
      (originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
        (rationalArithmeticOriginalPrime a p hp F)) (rationalTraceOriginalFiniteRep a q σ F hker),
      rationalTraceOriginalLocalUnitH1Cup a q σ F hker p hp z
        (rationalTraceOriginalLocalHomH1Equiv a q σ F hker p hp hσ hn u) =
      rationalTraceOriginalLocalUnitH1Cup a q σ F hker p hp z
        (rationalTraceOriginalLocalHomH1Equiv a q σ F hker p hp hσ hn v)) : u = v := by
  apply rationalTraceOriginalMappedHomH1_eq_of_cups a q σ F hker p hp hσ hn
  intro c
  exact h (Submodule.Quotient.mk (rationalTraceOriginalCoefficientCocycle a q σ F hker p hp c))

end
end Dubon2026
