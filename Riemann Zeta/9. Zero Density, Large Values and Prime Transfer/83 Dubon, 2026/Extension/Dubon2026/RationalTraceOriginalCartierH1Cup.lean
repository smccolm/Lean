import Dubon2026.RationalTraceOriginalLocalH1Cup
import Dubon2026.RationalTraceOriginalCartierH1

/-! The prescribed coherent trace-dual class has the exact retained
source cup, on the original completion. This supplies the right-hand
cup comparison needed to identify DUB-17's assembled S-place class. -/
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

attribute [local instance 1100] Submodule.module Submodule.Quotient.module
attribute [local instance] exceptionalTraceRootTopology exceptionalTraceRootDiscrete
  exceptionalTraceUnitTopology exceptionalTraceUnitDiscrete

private theorem original_cup_mk
    (c : continuousRepresentationCocyclesOne (rationalTraceOriginalLocalHomRep a q σ F hker p hp))
    (z : galoisTowerLocalCoefficientH1 ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
      ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F)
      (rationalPrimeLocalClosure p hp) Gal(F/ℚ)
      (originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
        (rationalArithmeticOriginalPrime a p hp F)) (rationalTraceOriginalFiniteRep a q σ F hker)) :
    rationalTraceOriginalLocalUnitH1Cup a q σ F hker p hp z (Submodule.Quotient.mk c) =
      galoisTowerLocalUnitCup ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
      ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F)
      (rationalPrimeLocalClosure p hp) Gal(F/ℚ)
      (originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
        (rationalArithmeticOriginalPrime a p hp F)) (rationalTraceOriginalFiniteRep a q σ F hker) c z := rfl

/-- The original Cartier H1 representative has exactly its source evaluation cup. -/
theorem rationalTraceOriginalCartierH1_cup
    (c : rationalTraceOriginalCartierSourceCocycles a q σ p hp)
    (z : galoisTowerLocalCoefficientH1 ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
      ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F)
      (rationalPrimeLocalClosure p hp) Gal(F/ℚ)
      (originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
        (rationalArithmeticOriginalPrime a p hp F)) (rationalTraceOriginalFiniteRep a q σ F hker)) :
    rationalTraceOriginalLocalUnitH1Cup a q σ F hker p hp z
      (rationalTraceOriginalLocalHomH1Equiv a q σ F hker p hp hσ hn
        (rationalPrimeTraceUnitH1Equiv p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp))
          (hσ.comp (rationalPrimeArithmeticRestriction a p hp).continuous) hn (Submodule.Quotient.mk c))) =
      galoisTowerLocalUnitCup ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
      ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F)
      (rationalPrimeLocalClosure p hp) Gal(F/ℚ)
      (originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
        (rationalArithmeticOriginalPrime a p hp F)) (rationalTraceOriginalFiniteRep a q σ F hker)
        (rationalTraceOriginalCartierAdicCocycle a q σ F hker p hp hn c) z := by
  exact (congrArg (fun x => rationalTraceOriginalLocalUnitH1Cup a q σ F hker p hp z x)
    (rationalTraceOriginalCartierH1_mk a q σ F hker p hp hσ hn c)).trans
    (original_cup_mk a q σ F hker p hp _ z)

/-- The coherent original trace-dual H1 class has exactly the source's
Cartier evaluation cup, with its proved arithmetic normalization. -/
theorem rationalTraceOriginalCoherentCartierH1_cup
    (hqa : (q : 𝓞 ℚ) ∣ a)
    (c : rationalTraceOriginalCartierSourceCocycles a q σ p hp)
    (z : galoisTowerLocalCoefficientH1 ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
      ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F)
      (rationalPrimeLocalClosure p hp) Gal(F/ℚ)
      (originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
        (rationalArithmeticOriginalPrime a p hp F)) (rationalTraceOriginalFiniteRep a q σ F hker)) :
    rationalTraceOriginalLocalUnitH1Cup a q σ F hker p hp z
      (rationalTraceOriginalLocalHomH1Equiv a q σ F hker p hp hσ hn
        (rationalPrimeTraceUnitH1Equiv p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp))
          (hσ.comp (rationalPrimeArithmeticRestriction a p hp).continuous) hn
          (rationalArithmeticLocalNormalizationScalar a q hqa p hp • Submodule.Quotient.mk c))) =
      galoisTowerLocalUnitCup ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
      ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F)
      (rationalPrimeLocalClosure p hp) Gal(F/ℚ)
      (originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
        (rationalArithmeticOriginalPrime a p hp F)) (rationalTraceOriginalFiniteRep a q σ F hker)
        (rationalTraceOriginalCartierAdicCocycle a q σ F hker p hp hn
          (rationalTraceCoherentCartierSourceCocycle a q hqa σ p hp c)) z := by
  exact (congrArg (fun x => rationalTraceOriginalLocalUnitH1Cup a q σ F hker p hp z x)
    (rationalTraceOriginalCoherentCartierH1_mk a q σ F hker p hp hσ hn hqa c)).trans
    (original_cup_mk a q σ F hker p hp _ z)

end
end Dubon2026
