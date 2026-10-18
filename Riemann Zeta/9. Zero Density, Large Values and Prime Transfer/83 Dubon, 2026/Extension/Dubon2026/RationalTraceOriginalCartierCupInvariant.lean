import Dubon2026.RationalTraceOriginalCupBaseChange
import Dubon2026.RationalPrimeTraceUnitCupInvariant
/-! The original-completion Cartier cup has exactly minus the source
scalar trace-cup invariant. The actual field comparison, Cartier duality,
reversed-order sign and root normalization are all proved, supplying the
local normalization obligation in DUB-17's reverse-localization total. -/
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
  rationalOriginalCompletionValuationExtension

/-- The original finite root coefficient retains its standard discrete topology. -/
local instance traceCartierInvariantRootTopology : TopologicalSpace
    (galoisRootOfUnityRepresentation (K := rationalPrimeLocalField p hp)
      (Ω := rationalPrimeLocalClosure p hp) q) := ⊥

/-- The selected root coefficient topology is discrete. -/
local instance traceCartierInvariantRootDiscrete : DiscreteTopology
    (galoisRootOfUnityRepresentation (K := rationalPrimeLocalField p hp)
      (Ω := rationalPrimeLocalClosure p hp) q) := ⟨rfl⟩

/-- The actual Cartier relation cup has the original scalar trace-cup
normalization, including the coefficient-first cup's minus sign. -/
theorem rationalTraceOriginalCartierCup_invariant
    (c : rationalTraceOriginalCartierSourceCocycles a q σ p hp)
    (d : continuousRepresentationCocyclesOne (rationalPrimeTraceZeroIntegerRep p hp q
      (σ.comp (rationalPrimeArithmeticRestriction a p hp)))) :
    localFieldContinuousH2InvariantEquiv ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
      (rationalPrimeLocalClosure p hp)
      (galoisTowerLocalUnitCup ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
        ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F) (rationalPrimeLocalClosure p hp)
        Gal(F/ℚ) (originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
          (rationalArithmeticOriginalPrime a p hp F)) (rationalTraceOriginalFiniteRep a q σ F hker)
        (rationalTraceOriginalCartierAdicCocycle a q σ F hker p hp hn c)
        (Quotient.mk _ (rationalTraceOriginalCoefficientCocycle a q σ F hker p hp d))) =
      -rationalCyclicInvariant q
        (rationalPrimeTraceH1ScalarCup p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp))
          (hσ.comp (rationalPrimeArithmeticRestriction a p hp).continuous)
          (Quotient.mk _ c)
          ((rationalPrimeTraceIntegerH1Equiv p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp))
            (hσ.comp (rationalPrimeArithmeticRestriction a p hp).continuous)).symm
              (Quotient.mk _ d))) := by
  let du := rationalPrimeTraceUnitCocycleEquiv p hp q
    (σ.comp (rationalPrimeArithmeticRestriction a p hp)) hn c
  have hb := rationalTraceOriginalLocalCup_baseChange a q σ F hker p hp hσ hn d du
  refine (rationalOriginalPrimeCompletion_invariant p hp _).symm.trans ?_
  refine (congrArg (localFieldContinuousH2InvariantEquiv
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)) hb).trans ?_
  have h := rationalPrimeTraceUnitEvaluationCup_invariant p hp q
    (σ.comp (rationalPrimeArithmeticRestriction a p hp))
    (hσ.comp (rationalPrimeArithmeticRestriction a p hp).continuous) hn
    (Quotient.mk _ c)
    ((rationalPrimeTraceIntegerH1Equiv p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp))
      (hσ.comp (rationalPrimeArithmeticRestriction a p hp).continuous)).symm (Quotient.mk _ d))
  simpa only [AddEquiv.apply_symm_apply] using h

end
end Dubon2026

