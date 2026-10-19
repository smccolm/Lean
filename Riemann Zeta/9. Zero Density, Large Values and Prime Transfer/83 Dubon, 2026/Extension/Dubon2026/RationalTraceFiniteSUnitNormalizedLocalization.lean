import Dubon2026.RationalTraceFiniteSUnitLocalizationComparison

/-! Compose the proved finite S-unit localization square with the original
trace-dual normalization. This is the exact map needed to recover the
original global class from the finite correction on DUB-17's chain. -/
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

/-- Finite S-unit localization is the normalized original trace-dual restriction. -/
theorem rationalTraceFiniteSUnitH1_normalized_localization
    (x : RationalTraceFiniteSUnitHomH1 a ha q σ F hker) :
    rationalPrimeTraceUnitH1Equiv p hp q
      (σ.comp (rationalPrimeArithmeticRestriction a p hp))
      (hσ.comp (rationalPrimeArithmeticRestriction a p hp).continuous) hn
      (rationalArithmeticLocalNormalizationScalar a q hqa p hp •
        rationalPrimeCyclotomicAdjointH1Restriction a q hqa p hp σ hσ
          (rationalTraceFiniteSUnitHomH1Equiv a ha q σ F hker hσ hqa hn x)) =
    rationalTraceFiniteLocalHomH1Equiv a q σ F hker p hp hσ hn
      (arithmeticFiniteSUnitLocalH1Map a ha F (rationalTraceOriginalFiniteRep a q σ F hker) p hp x) := by
  exact ((rationalTraceFiniteSUnitLocalization_comparison a ha q σ F hker hσ hqa hn p hp x).trans
    (rationalTraceSUnitLocalH1Map_traceDual a ha q σ hσ hqa hn p hp
      (rationalTraceFiniteSUnitHomH1Equiv a ha q σ F hker hσ hqa hn x))).symm

end
end Dubon2026
