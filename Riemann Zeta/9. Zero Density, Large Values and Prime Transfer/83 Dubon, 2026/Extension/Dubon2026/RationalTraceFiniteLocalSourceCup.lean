import Dubon2026.RationalTraceFiniteLocalSourceInflation
import Dubon2026.RationalTraceOriginalSourceCupInvariant
import Dubon2026.OriginalAdicFiniteCupInvariant
/-! Normalize the actual finite-local Cartier cup on its original source class. This is the termwise identity needed for DUB-17's canonical-total vanishing. -/
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

attribute [local instance] rationalOriginalCompletionValuation rationalOriginalCompletionLocalField
  rationalOriginalCompletionValuationExtension traceCartierInvariantRootTopology traceCartierInvariantRootDiscrete

/-- The required normalized scalar value on the actual source restriction. -/
def rationalTraceSourceScalarCupInvariant
    (d : rationalTraceOriginalCartierSourceCocycles a q σ p hp)
    (c : continuousTraceZeroAdjointCocycles σ) : AddCircle (1 : ℚ) :=
  -rationalCyclicInvariant q
    (rationalPrimeTraceH1ScalarCup p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp))
      (hσ.comp (rationalPrimeArithmeticRestriction a p hp).continuous)
      (Quotient.mk _ d)
      (continuousTraceZeroH1Restriction σ hσ (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
        (rationalPrimeArithmeticRestriction a p hp).continuous (Quotient.mk _ c)))

attribute [local instance 1100] finiteLocalRelationCoefficientTopology
  finiteLocalRelationCoefficientDiscrete finiteLocalRelationCoefficientContinuousSMul
attribute [local instance] rationalTraceCompletionCoefficientTopology
  rationalTraceCompletionCoefficientDiscrete traceFiniteSourceContinuousSMul

/-- The original finite-local cup equals the negative scalar trace cup
on the restriction of the same source cocycle. -/
theorem rationalTraceFiniteLocalCupInvariant_eq_source
    (d : rationalTraceOriginalCartierSourceCocycles a q σ p hp)
    (y : groupCohomology (rationalTraceOriginalFiniteRep a q σ F hker) 1)
    (x : galoisTowerFiniteLocalCoefficientH1
      ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
      ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F) Gal(F/ℚ)
      (originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
        (rationalArithmeticOriginalPrime a p hp F)) (rationalTraceOriginalFiniteRep a q σ F hker))
    (hx : @continuousH1ToAlgebraic ℤ
      Gal((rationalArithmeticOriginalPrime a p hp F).adicCompletion F /
        (rationalOriginalPrimePlace p hp).adicCompletion ℚ) _ _ _ _
      (Rep.res (originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
        (rationalArithmeticOriginalPrime a p hp F)) (rationalTraceOriginalFiniteRep a q σ F hker))
      ⊥ _ _ continuous_of_discreteTopology x =
      groupCohomology.map
        (originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
          (rationalArithmeticOriginalPrime a p hp F))
        (𝟙 (Rep.res (originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
          (rationalArithmeticOriginalPrime a p hp F)) (rationalTraceOriginalFiniteRep a q σ F hker))) 1 y)
    (c : continuousTraceZeroAdjointCocycles σ)
    (hc : @continuousH1ToAlgebraic ℤ (rationalArithmeticGaloisGroup a) _ _ _ _
      (rationalArithmeticTraceZeroIntegerRep a q σ)
      (rationalTraceCompletionCoefficientTopology a q σ) _ _
      (rationalTraceIntegerAction_continuous a q σ hσ)
      (rationalArithmeticTraceIntegerH1Equiv a q σ hσ (Quotient.mk _ c)) =
      groupCohomology.map (AlgEquiv.restrictNormalHom F)
        (rationalTraceFiniteSourceCoefficientMap a q σ F hker) 1 y) :
    originalAdicFiniteLocalCupInvariant ℚ F (rationalOriginalPrimePlace p hp)
      (rationalArithmeticOriginalPrime a p hp F) (rationalPrimeLocalClosure p hp)
      (rationalTraceOriginalFiniteRep a q σ F hker)
      (rationalTraceOriginalCartierAdicCocycle a q σ F hker p hp hn d) x =
      rationalTraceSourceScalarCupInvariant a q σ p hp hσ d c := by
  unfold originalAdicFiniteLocalCupInvariant
  rw [rationalTraceFiniteLocalH1Inflation_eq_source a q σ F hker p hp hσ y x hx c hc]
  exact rationalTraceOriginalSourceCup_invariant a q σ F hker p hp hσ hn d c

end
end Dubon2026
