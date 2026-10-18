import Dubon2026.RationalTraceExceptionalCompletionInvariants
import Dubon2026.RationalTraceExceptionalCoherentCocycle
import Dubon2026.RationalTraceExceptionalFiniteCupValue
import Dubon2026.RationalTraceCoherentExceptionalSum
import Dubon2026.RationalTraceFiniteSourceCocycle
import Dubon2026.RationalTraceFiniteLocalSourceCup
/-! The original coherent annihilator condition kills the finite-local Cartier cup sum on every finite H1 input. This is the source-side vanishing needed by DUB-17's canonical-total criterion. -/
namespace Dubon2026
noncomputable section
open CategoryTheory IsDedekindDomain
open scoped NumberField BigOperators
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV1 Rep.hV2
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitCompletionNumberField arithmeticOrbitCompletionBaseAlgebra
  arithmeticOrbitCompletionValuation arithmeticOrbitCompletionTopology arithmeticOrbitCompletionLocalField
  arithmeticOrbitCompletionValuationExtension arithmeticOrbitCompletionUniformity arithmeticOrbitCompletionUniformAdd
  arithmeticOrbitCompletionTargetAlgebra arithmeticOrbitCompletionClosureAlgebra arithmeticOrbitCompletionGlobalAlgebra
  rationalOriginalCompletionTargetAlgebra rationalOriginalCompletionClosureAlgebra
  rationalOriginalCompletionClosureTower rationalOriginalCompletionGalois rationalArithmeticOriginalPrimeLiesOver
  originalAdicRelationCompletionAlgebra originalAdicLocalRelationGalois originalAdicLocalRelationCupFinite
  rationalArithmeticOriginalCompletion_closureTower rationalArithmeticOriginalFiniteGalois
  rationalTraceCompletionArithmeticGalois traceOriginalFiniteRepFinite rationalExceptionalIndexedPrimeLiesOver
  originalAdicRelationCupHomTopology originalAdicRelationCupHomDiscrete originalAdicRelationCupHomContinuousSMul

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (ha : a ≠ 0) (q : ℕ) [Fact q.Prime]
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
  (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (hker : ∀ u : rationalArithmeticGaloisGroup a,
    AlgEquiv.restrictNormalHom F u = 1 →
    ∀ x : rationalArithmeticTraceZeroIntegerRep a q σ,
      (rationalArithmeticTraceZeroIntegerRep a q σ).ρ u x = x)
  (hn : (Fintype.card ι : ZMod q) ≠ 0)
  (d : ∀ p : rationalArithmeticExceptionalPrimes a ha,
    rationalTraceOriginalCartierSourceCocycles a q σ p.val.val p.val.property)

attribute [local instance] traceExceptionalHomTopology traceExceptionalHomDiscrete
  traceExceptionalHomContinuousSMul indexedPrimeRelationCosets


attribute [local instance] finiteLocalRelationCoefficientTopology
  finiteLocalRelationCoefficientDiscrete finiteLocalRelationCoefficientContinuousSMul
  localRelationCupUnitsTopology localRelationCupUnitsDiscrete localRelationCupUnitsContinuousSMul
  exceptionalTraceRootTopology exceptionalTraceRootDiscrete
  exceptionalTraceUnitTopology exceptionalTraceUnitDiscrete

variable (hσ : Continuous σ) (hqa : (q : 𝓞 ℚ) ∣ a)

/-- Coherent orthogonality on the original global source implies zero
for the actual finite-local Cartier sum, using one constructed source
cocycle for all primes and the derived finite-lift comparisons. -/
theorem rationalTraceExceptionalFiniteCupSum_eq_zero
    (hann : ∀ y : ContinuousTraceZeroAdjointH1 σ hσ,
      rationalArithmeticExceptionalTracePairing a q hqa ha σ hσ
        (rationalTraceExceptionalSourceH1 a ha q σ hσ d)
        (rationalArithmeticTraceH1Localization a q ha σ hσ y) = 0)
    (y : groupCohomology (rationalTraceOriginalFiniteRep a q σ F hker) 1)
    (x : ∀ p : rationalArithmeticExceptionalPrimes a ha,
      rationalTraceExceptionalFiniteLocalH1 a ha q σ F hker p)
    (hx : ∀ p : rationalArithmeticExceptionalPrimes a ha,
      continuousH1ToAlgebraic
        (Rep.res (originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p.val.val p.val.property)
          (rationalArithmeticOriginalPrime a p.val.val p.val.property F)) (rationalTraceOriginalFiniteRep a q σ F hker))
        continuous_of_discreteTopology (x p) =
        groupCohomology.map
          (originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p.val.val p.val.property)
            (rationalArithmeticOriginalPrime a p.val.val p.val.property F))
          (𝟙 (Rep.res
            (originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p.val.val p.val.property)
              (rationalArithmeticOriginalPrime a p.val.val p.val.property F))
            (rationalTraceOriginalFiniteRep a q σ F hker))) 1 y) :
    (∑ p : rationalArithmeticExceptionalPrimes a ha,
      rationalTraceExceptionalCoherentFiniteCupValue a ha q σ F hker hn d hqa p (x p)) = 0 := by
  obtain ⟨c, hc⟩ := rationalTraceFiniteStageH1_exists_original_cocycle a q σ F hker hσ y
  have hsum : (∑ p : rationalArithmeticExceptionalPrimes a ha,
      rationalTraceExceptionalCoherentFiniteCupValue a ha q σ F hker hn d hqa p (x p)) =
      ∑ p : rationalArithmeticExceptionalPrimes a ha,
        rationalTraceSourceScalarCupInvariant a q σ p.val.val p.val.property hσ
          (rationalTraceCoherentCartierSourceCocycle a q hqa σ p.val.val p.val.property (d p)) c := by
    apply Finset.sum_congr rfl
    intro p _
    exact rationalTraceFiniteLocalCupInvariant_eq_source a q σ F hker p.val.val p.val.property hσ hn
      (rationalTraceCoherentCartierSourceCocycle a q hqa σ p.val.val p.val.property (d p))
      y (x p) (hx p) c hc
  exact hsum.trans (rationalTraceCoherentSourceScalarCup_sum_eq_zero a ha q σ hσ hqa d c hann)

end
end Dubon2026
