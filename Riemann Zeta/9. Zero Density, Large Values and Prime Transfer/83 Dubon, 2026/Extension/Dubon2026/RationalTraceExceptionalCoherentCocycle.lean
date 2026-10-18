import Dubon2026.RationalTraceExceptionalCocycles
import Dubon2026.RationalTraceCoherentSourceCup
/-! Construct the actual exceptional Cartier family with the proved coherent root normalization. This retains DUB-17's original dependent local coefficient types. -/
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


variable (hqa : (q : 𝓞 ℚ) ∣ a)

attribute [local instance] traceExceptionalHomTopology traceExceptionalHomDiscrete
  traceExceptionalHomContinuousSMul

/-- The actual coherent source cocycles at the unchanged exceptional primes. -/
def rationalTraceExceptionalCoherentSourceCocycles (p : rationalArithmeticExceptionalPrimes a ha) :
    rationalTraceOriginalCartierSourceCocycles a q σ p.val.val p.val.property :=
  rationalTraceCoherentCartierSourceCocycle a q hqa σ p.val.val p.val.property (d p)

/-- Apply the original Cartier construction to the coherently scaled
source family at each original chosen upper prime. -/
def rationalTraceExceptionalCoherentCartierCocycle (p : rationalArithmeticExceptionalPrimes a ha) :
    continuousRepresentationCocyclesOne (rationalTraceExceptionalLocalHomRep a ha q σ F hker p) :=
  rationalTraceExceptionalCartierCocycle a ha q σ F hker hn
    (rationalTraceExceptionalCoherentSourceCocycles a ha q σ d hqa) p

end
end Dubon2026
