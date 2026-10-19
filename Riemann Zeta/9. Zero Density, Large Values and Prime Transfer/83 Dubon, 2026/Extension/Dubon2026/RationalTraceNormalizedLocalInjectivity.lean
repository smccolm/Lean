import Dubon2026.RationalTraceFiniteSUnitNormalizedLocalization

/-! The proved nonzero arithmetic normalization can be cancelled on the
original local trace-dual H1. This removes the coordinate factor after
the finite-correction and source-cup comparisons on DUB-17's chain. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV1 Rep.hV2
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  rationalTraceCompletionArithmeticGalois rationalArithmeticOriginalFiniteGalois

attribute [local instance] rationalTraceFiniteDualClassAlgebraicClosure

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (ha : a ≠ 0) (q : ℕ) [Fact q.Prime]
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
  (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (hker : ∀ u : rationalArithmeticGaloisGroup a,
    AlgEquiv.restrictNormalHom F u = 1 →
    ∀ x : rationalArithmeticTraceZeroIntegerRep a q σ,
      (rationalArithmeticTraceZeroIntegerRep a q σ).ρ u x = x)
  (hσ : Continuous σ) (hqa : (q : 𝓞 ℚ) ∣ a)
  (hn : (Fintype.card ι : ZMod q) ≠ 0)


attribute [local instance] finiteGlobalTraceHomTopology finiteGlobalTraceHomDiscrete
  finiteGlobalTraceHomContinuousSMul originalGlobalTraceHomTopology originalGlobalTraceHomDiscrete
  originalGlobalTraceHomContinuousSMul finiteLocalTraceCoefficientFinite
  finiteLocalTraceCoefficientModuleFinite finiteLocalTraceHomTopology finiteLocalTraceHomDiscrete
  finiteLocalTraceHomContinuousSMul finiteLocalPrimeHomTopology finiteLocalPrimeHomDiscrete
  finiteLocalPrimeHomContinuousSMul
variable (p : ℕ) (hp : p.Prime)

attribute [local instance 1100] Submodule.module Submodule.Quotient.module

attribute [local instance 1100] Submodule.module Submodule.Quotient.module


attribute [local instance] exceptionalTraceRootTopology exceptionalTraceRootDiscrete
  exceptionalTraceUnitTopology exceptionalTraceUnitDiscrete


/-- The normalized prime-local Cartier map is injective on the original H1. -/
theorem rationalTraceNormalizedPrimeUnitH1_injective :
    Function.Injective (fun x : rationalArithmeticPrimeTraceDualH1Module a q σ hσ ⟨p, hp⟩ =>
      rationalPrimeTraceUnitH1Equiv p hp q
        (σ.comp (rationalPrimeArithmeticRestriction a p hp))
        (hσ.comp (rationalPrimeArithmeticRestriction a p hp).continuous) hn
        (rationalArithmeticLocalNormalizationScalar a q hqa p hp • x)) := by
  intro x y h
  apply smul_right_injective (rationalArithmeticPrimeTraceDualH1Module a q σ hσ ⟨p, hp⟩)
    (rationalArithmeticLocalNormalizationScalar_ne_zero a q hqa p hp)
  exact (rationalPrimeTraceUnitH1Equiv p hp q
    (σ.comp (rationalPrimeArithmeticRestriction a p hp))
    (hσ.comp (rationalPrimeArithmeticRestriction a p hp).continuous) hn).injective h

end
end Dubon2026
