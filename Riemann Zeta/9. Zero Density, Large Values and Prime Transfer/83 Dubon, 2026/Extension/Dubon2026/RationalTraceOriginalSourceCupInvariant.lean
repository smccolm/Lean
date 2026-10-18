import Dubon2026.RationalTraceOriginalCartierCupInvariant
import Dubon2026.RationalTracePrimeIntegerCocycle
/-! The original source trace-zero cocycle gives the exact normalized
Cartier cup at each prime. Its source H1 restriction, completion transport,
coefficient conversion and sign are the original constructed ones. This
serves DUB-17's scalar-annihilator to canonical-total implication. -/
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

attribute [local instance] rationalOriginalCompletionValuation rationalOriginalCompletionLocalField
  rationalOriginalCompletionValuationExtension traceCartierInvariantRootTopology traceCartierInvariantRootDiscrete

/-- The normalized local Cartier cup on the actual source representative
is minus its original prime-restricted scalar trace cup. -/
theorem rationalTraceOriginalSourceCup_invariant
    (c : rationalTraceOriginalCartierSourceCocycles a q σ p hp)
    (y : continuousTraceZeroAdjointCocycles σ) :
    localFieldContinuousH2InvariantEquiv ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
      (rationalPrimeLocalClosure p hp)
      (galoisTowerLocalUnitCup ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
        ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F) (rationalPrimeLocalClosure p hp)
        Gal(F/ℚ) (originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
          (rationalArithmeticOriginalPrime a p hp F)) (rationalTraceOriginalFiniteRep a q σ F hker)
        (rationalTraceOriginalCartierAdicCocycle a q σ F hker p hp hn c)
        (Quotient.mk _ (rationalTraceOriginalCoefficientCocycle a q σ F hker p hp
          (rationalTracePrimeIntegerCocycle a q σ p hp y)))) =
      -rationalCyclicInvariant q
        (rationalPrimeTraceH1ScalarCup p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp))
          (hσ.comp (rationalPrimeArithmeticRestriction a p hp).continuous)
          (Quotient.mk _ c)
          (continuousTraceZeroH1Restriction σ hσ (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
            (rationalPrimeArithmeticRestriction a p hp).continuous (Quotient.mk _ y))) := by
  have h := rationalTraceOriginalCartierCup_invariant a q σ F hker p hp hσ hn c
    (rationalTracePrimeIntegerCocycle a q σ p hp y)
  have hclass := congrArg
    (rationalPrimeTraceIntegerH1Equiv p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp))
      (hσ.comp (rationalPrimeArithmeticRestriction a p hp).continuous)).symm
    (rationalTracePrimeIntegerCocycle_class a q σ p hp hσ y).symm
  simp only [AddEquiv.symm_apply_apply] at hclass
  exact h.trans (congrArg (fun z => -rationalCyclicInvariant q
    (rationalPrimeTraceH1ScalarCup p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp))
      (hσ.comp (rationalPrimeArithmeticRestriction a p hp).continuous)
      (Quotient.mk _ c) z)) hclass)

end
end Dubon2026

