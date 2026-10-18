import Dubon2026.RationalTraceOriginalCoefficientCocycle
import Dubon2026.RationalTraceOriginalCartierCocycle
import Dubon2026.RationalPrimeTraceUnitCup
/-! Compare the original-completion evaluation cup to the literal prime-local
cup. The proof uses the existing cocycle formula and actual base-change map;
it supplies the normalization bridge needed by DUB-17's Cartier total. -/
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

/-- The actual completion base change sends the transported evaluation
cup to the original prime-local cup on the same two cocycle representatives. -/
theorem rationalTraceOriginalLocalCup_baseChange
    (c : continuousRepresentationCocyclesOne (rationalPrimeTraceZeroIntegerRep p hp q
      (σ.comp (rationalPrimeArithmeticRestriction a p hp))))
    (d : continuousRepresentationCocyclesOne (rationalPrimeTraceUnitHomRep p hp q
      (σ.comp (rationalPrimeArithmeticRestriction a p hp)))) :
    continuousGaloisUnitBaseChangeH2 ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
      (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) (rationalPrimeLocalClosure p hp)
      (galoisTowerLocalUnitCup ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
        ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F) (rationalPrimeLocalClosure p hp)
        Gal(F/ℚ) (originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
          (rationalArithmeticOriginalPrime a p hp F)) (rationalTraceOriginalFiniteRep a q σ F hker)
        (rationalTraceOriginalLocalHomCocycleMap a q σ F hker p hp d)
        (Submodule.Quotient.mk (rationalTraceOriginalCoefficientCocycle a q σ F hker p hp c))) =
      rationalPrimeTraceUnitEvaluationCup p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp))
        (hσ.comp (rationalPrimeArithmeticRestriction a p hp).continuous) hn
        (Submodule.Quotient.mk c) (Submodule.Quotient.mk d) := by
  apply congrArg ((continuousRepresentationCoboundariesTwo
    (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))
    (discreteGaloisUnitAction_continuous
      (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp))).mkQ)
  apply Subtype.ext
  apply Subtype.ext
  funext z
  change Units.map (algebraMap (rationalPrimeLocalClosure p hp) (rationalPrimeLocalClosure p hp)).toMonoidHom
    (Additive.toMul (Rep.toAdditive
      (originalInternalHomEvaluation (rationalTraceOriginalLocalCoefficientRep a q σ F hker p hp)
        (Rep.ofAlgebraAutOnUnits ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
          (rationalPrimeLocalClosure p hp))
        ((rationalTraceOriginalCoefficientCocycle a q σ F hker p hp c).val
          (galoisBaseChangeRestriction ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
            (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) (rationalPrimeLocalClosure p hp) z.1))
        ((rationalTraceOriginalLocalHomRep a q σ F hker p hp).ρ
        (galoisBaseChangeRestriction ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
          (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) (rationalPrimeLocalClosure p hp) z.1)
        ((rationalTraceOriginalLocalHomCocycleMap a q σ F hker p hp d).val
          (galoisBaseChangeRestriction ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
            (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) (rationalPrimeLocalClosure p hp) z.2)))))) =
    Additive.toMul (Rep.toAdditive
      (originalInternalHomEvaluation
        (rationalPrimeTraceZeroIntegerRep p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp)))
        (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))
        (c.val z.1)
        ((rationalPrimeTraceUnitHomRep p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp))).ρ z.1
          (d.val z.2))))
  simp only [rationalOriginalCompletionGaloisEquiv_baseChange p hp,
    rationalTraceOriginalLocalHomCocycleMap_apply a q σ F hker p hp d,
    rationalTraceOriginalCoefficientCocycle_apply a q σ F hker p hp c,
    rationalTraceOriginalCompletionHom_action a q σ F hker p hp,
    MulEquiv.symm_apply_apply]
  apply Units.ext
  rfl

end
end Dubon2026

