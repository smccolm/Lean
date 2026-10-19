import Dubon2026.RationalTraceOriginalCartierH1

/-! The coherent source cocycle represents precisely the normalized
prime-local unit-Hom H1 class. The already proved original Cartier H1
identities and actual completion equivalence discharge the normalization
without re-expanding scalar structures on DUB-17's source-class chain. -/
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


include F hker in
/-- The coherent source representative gives exactly the normalized
original unit-Hom class, by injectivity of the actual completion comparison. -/
theorem rationalTraceCoherentUnitH1_mk
    (hqa : (q : 𝓞 ℚ) ∣ a)
    (c : rationalTraceOriginalCartierSourceCocycles a q σ p hp) :
    rationalPrimeTraceUnitH1Equiv p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp))
      (hσ.comp (rationalPrimeArithmeticRestriction a p hp).continuous) hn
      (Submodule.Quotient.mk (rationalTraceCoherentCartierSourceCocycle a q hqa σ p hp c)) =
    rationalPrimeTraceUnitH1Equiv p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp))
      (hσ.comp (rationalPrimeArithmeticRestriction a p hp).continuous) hn
      (rationalArithmeticLocalNormalizationScalar a q hqa p hp • Submodule.Quotient.mk c) := by
  apply (rationalTraceOriginalLocalHomH1Equiv a q σ F hker p hp hσ hn).injective
  exact (rationalTraceOriginalCartierH1_mk a q σ F hker p hp hσ hn
    (rationalTraceCoherentCartierSourceCocycle a q hqa σ p hp c)).trans
    (rationalTraceOriginalCoherentCartierH1_mk a q σ F hker p hp hσ hn hqa c).symm

end
end Dubon2026
