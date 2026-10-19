import Dubon2026.RationalTraceOriginalLocalHomH1
import Dubon2026.RationalTraceOriginalCupBaseChange

/-! The original-completion local unit cup on genuine H1 classes, with
its exact change to the original prime-local cup. This supplies the
completion-identification edge in DUB-17's prescribed local recovery. -/
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

/-- The actual original-completion evaluation cup, on both original H1 quotients. -/
def rationalTraceOriginalLocalUnitH1Cup :=
  let A := rationalTraceOriginalLocalCoefficientRep a q σ F hker p hp
  let U := rationalTraceOriginalLocalHomRep a q σ F hker p hp
  let D := Rep.ofAlgebraAutOnUnits ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
    (rationalPrimeLocalClosure p hp)
  continuousH1Cup A U D (originalInternalHomEvaluation A D)
    (originalInternalHomEvaluation_equivariant A D) continuous_of_discreteTopology
    (galoisTowerRestrictedCoefficientAction_continuous ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
    ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F) (rationalPrimeLocalClosure p hp)
    Gal(F/ℚ) (originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
      (rationalArithmeticOriginalPrime a p hp F)) (rationalTraceOriginalFiniteRep a q σ F hker))
    (rationalTraceOriginalLocalHomAction_continuous a q σ F hker p hp)
    (discreteGaloisUnitAction_continuous
      (K := (rationalOriginalPrimePlace p hp).adicCompletion ℚ) (Ω := rationalPrimeLocalClosure p hp))

/-- The existing cocycle cup comparison descends through the actual
original-completion Hom H1 equivalence, retaining every coefficient value. -/
theorem rationalTraceOriginalLocalUnitH1Cup_baseChange
    (c : continuousRepresentationCocyclesOne (rationalPrimeTraceZeroIntegerRep p hp q
      (σ.comp (rationalPrimeArithmeticRestriction a p hp))))
    (u : ContinuousRepresentationH1 (rationalPrimeTraceUnitHomRep p hp q
      (σ.comp (rationalPrimeArithmeticRestriction a p hp)))
      (rationalPrimeTraceUnitHomAction_continuous p hp q
        (σ.comp (rationalPrimeArithmeticRestriction a p hp))
        (hσ.comp (rationalPrimeArithmeticRestriction a p hp).continuous) hn)) :
    continuousGaloisUnitBaseChangeH2 ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
      (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) (rationalPrimeLocalClosure p hp)
      (rationalTraceOriginalLocalUnitH1Cup a q σ F hker p hp
        (Submodule.Quotient.mk (rationalTraceOriginalCoefficientCocycle a q σ F hker p hp c))
        (rationalTraceOriginalLocalHomH1Equiv a q σ F hker p hp hσ hn u)) =
      rationalPrimeTraceUnitEvaluationCup p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp))
        (hσ.comp (rationalPrimeArithmeticRestriction a p hp).continuous) hn
        (Submodule.Quotient.mk c) u := by
  induction u using Submodule.Quotient.induction_on with
  | _ d =>
    have he := rationalTraceOriginalLocalHomH1Equiv_mk a q σ F hker p hp hσ hn d
    exact (congrArg (fun z =>
      continuousGaloisUnitBaseChangeH2 ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
        (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) (rationalPrimeLocalClosure p hp)
        (rationalTraceOriginalLocalUnitH1Cup a q σ F hker p hp
          (Submodule.Quotient.mk (rationalTraceOriginalCoefficientCocycle a q σ F hker p hp c)) z)) he).trans
      (rationalTraceOriginalLocalCup_baseChange a q σ F hker p hp hσ hn c d)

end
end Dubon2026
