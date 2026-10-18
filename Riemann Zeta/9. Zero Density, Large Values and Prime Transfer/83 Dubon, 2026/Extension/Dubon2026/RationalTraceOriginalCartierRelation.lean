import Dubon2026.RationalTraceOriginalLocalHomCocycle
import Dubon2026.RationalPrimeTraceUnitCocycle
import Dubon2026.OriginalAdicLocalUnitCupRealization
import Dubon2026.RationalTraceOriginalCartierCocycle

/-! Actual local Cartier cocycles in the original completion relation.
This is the local specialization required by DUB-17, before finite-family
assembly and the canonical total comparison. -/
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

attribute [local instance] traceOriginalFiniteRepFinite traceCartierOriginalHomTopology
  traceCartierOriginalHomDiscrete traceOriginalSourceHomContinuousSMul
  traceOriginalTargetHomTopology traceOriginalTargetHomDiscrete traceOriginalTargetHomContinuousSMul

variable (hn : (Fintype.card ι : ZMod q) ≠ 0)

/-- Every actual prime-local trace-dual cocycle has an original completion
relation morphism representing all of its continuous coefficient-first unit cups. -/
theorem rationalTraceOriginalCartierCocycle_exists_relation_cup
    (c : rationalTraceOriginalCartierSourceCocycles a q σ p hp) :
    let c' := @rationalTraceOriginalCartierAdicCocycle ι inferInstance inferInstance
      a q inferInstance σ F hker p hp hn c
    OriginalAdicLocalUnitCupRealization ℚ F
    (rationalOriginalPrimePlace p hp) (rationalArithmeticOriginalPrime a p hp F)
    (rationalPrimeLocalClosure p hp) (rationalTraceOriginalFiniteRep a q σ F hker)
    c' := by
  let c' := @rationalTraceOriginalCartierAdicCocycle ι inferInstance inferInstance
    a q inferInstance σ F hker p hp hn c
  exact originalAdicLocalUnitCocycle_exists_relation_cup ℚ F
    (rationalOriginalPrimePlace p hp) (rationalArithmeticOriginalPrime a p hp F)
    (rationalPrimeLocalClosure p hp) (rationalTraceOriginalFiniteRep a q σ F hker)
    c'

end
end Dubon2026

