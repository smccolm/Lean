import Dubon2026.RationalTraceOriginalLocalHomH1
import Dubon2026.RationalTraceCoherentSourceCup

/-! The actual original-completion Cartier cocycle represents the exact
image of its original trace-dual H1 class, retaining the proved arithmetic
normalization scalar needed for DUB-17's prescribed local restriction. -/
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

attribute [local instance] traceOriginalFiniteRepFinite
  traceCartierOriginalHomTopology traceCartierOriginalHomDiscrete
  traceOriginalSourceHomContinuousSMul traceOriginalTargetHomTopology
  traceOriginalTargetHomDiscrete traceOriginalTargetHomContinuousSMul


attribute [local instance 1100] Submodule.module Submodule.Quotient.module
attribute [local instance] exceptionalTraceRootTopology exceptionalTraceRootDiscrete
  exceptionalTraceUnitTopology exceptionalTraceUnitDiscrete
variable (hσ : Continuous σ) (hn : (Fintype.card ι : ZMod q) ≠ 0)

/-- The original Cartier cocycle represents the same trace-dual H1
class under the genuine coefficient and completion equivalences. -/
theorem rationalTraceOriginalCartierH1_mk
    (c : rationalTraceOriginalCartierSourceCocycles a q σ p hp) :
    rationalTraceOriginalLocalHomH1Equiv a q σ F hker p hp hσ hn
      (rationalPrimeTraceUnitH1Equiv p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp))
      (hσ.comp (rationalPrimeArithmeticRestriction a p hp).continuous) hn (Submodule.Quotient.mk c)) =
    Submodule.Quotient.mk (rationalTraceOriginalCartierAdicCocycle a q σ F hker p hp hn c) :=
  rationalTraceOriginalLocalHomH1Equiv_mk a q σ F hker p hp hσ hn
    (rationalPrimeTraceUnitCocycleEquiv p hp q
      (σ.comp (rationalPrimeArithmeticRestriction a p hp)) hn c)

/-- The source's coherent Cartier class is precisely the same original
trace-dual H1 class multiplied by the proved local normalization scalar. -/
theorem rationalTraceOriginalCoherentCartierH1_mk
    (hqa : (q : 𝓞 ℚ) ∣ a)
    (c : rationalTraceOriginalCartierSourceCocycles a q σ p hp) :
    rationalTraceOriginalLocalHomH1Equiv a q σ F hker p hp hσ hn
      (rationalPrimeTraceUnitH1Equiv p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp))
      (hσ.comp (rationalPrimeArithmeticRestriction a p hp).continuous) hn
        (rationalArithmeticLocalNormalizationScalar a q hqa p hp • Submodule.Quotient.mk c)) =
    Submodule.Quotient.mk (rationalTraceOriginalCartierAdicCocycle a q σ F hker p hp hn
      (rationalTraceCoherentCartierSourceCocycle a q hqa σ p hp c)) :=
  rationalTraceOriginalCartierH1_mk a q σ F hker p hp hσ hn
    (rationalTraceCoherentCartierSourceCocycle a q hqa σ p hp c)

end
end Dubon2026
