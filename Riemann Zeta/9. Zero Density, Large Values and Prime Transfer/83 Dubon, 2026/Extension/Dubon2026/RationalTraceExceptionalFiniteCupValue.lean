import Dubon2026.RationalTraceExceptionalCoherentCocycle
import Dubon2026.RationalTraceFiniteLocalSourceCup
/-! Name the exact original finite-local cup value at each exceptional prime, retaining the actual coherent Cartier cocycle. This keeps DUB-17's finite sum consumer on the same dependent completion types. -/
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
  traceExceptionalHomContinuousSMul


attribute [local instance] finiteLocalRelationCoefficientTopology
  finiteLocalRelationCoefficientDiscrete finiteLocalRelationCoefficientContinuousSMul
  localRelationCupUnitsTopology localRelationCupUnitsDiscrete localRelationCupUnitsContinuousSMul
  exceptionalTraceRootTopology exceptionalTraceRootDiscrete
  exceptionalTraceUnitTopology exceptionalTraceUnitDiscrete

variable (hσ : Continuous σ) (hqa : (q : 𝓞 ℚ) ∣ a)


/-- The original finite-local coefficient H1 at this exact exceptional prime. -/
abbrev rationalTraceExceptionalFiniteLocalH1
    (p : rationalArithmeticExceptionalPrimes a ha) :=
  galoisTowerFiniteLocalCoefficientH1
      ((rationalOriginalPrimePlace p.val.val p.val.property).adicCompletion ℚ)
      ((rationalArithmeticOriginalPrime a p.val.val p.val.property F).adicCompletion F) Gal(F/ℚ)
      (originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p.val.val p.val.property)
        (rationalArithmeticOriginalPrime a p.val.val p.val.property F))
      (rationalTraceOriginalFiniteRep a q σ F hker)

/-- The actual finite-local cup invariant of the coherent Cartier source
at this original exceptional prime and original finite field. -/
def rationalTraceExceptionalCoherentFiniteCupValue
    (p : rationalArithmeticExceptionalPrimes a ha)
    (x : rationalTraceExceptionalFiniteLocalH1 a ha q σ F hker p) : AddCircle (1 : ℚ) :=
  originalAdicFiniteLocalCupInvariant ℚ F (rationalOriginalPrimePlace p.val.val p.val.property)
    (rationalArithmeticOriginalPrime a p.val.val p.val.property F) (rationalPrimeLocalClosure p.val.val p.val.property)
    (rationalTraceOriginalFiniteRep a q σ F hker)
    (rationalTraceOriginalCartierAdicCocycle a q σ F hker p.val.val p.val.property hn
      (rationalTraceCoherentCartierSourceCocycle a q hqa σ p.val.val p.val.property (d p))) x

end
end Dubon2026
