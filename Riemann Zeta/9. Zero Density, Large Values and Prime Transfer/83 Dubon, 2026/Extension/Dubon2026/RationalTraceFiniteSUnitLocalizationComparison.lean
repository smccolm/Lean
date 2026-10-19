import Dubon2026.RationalTraceFiniteGlobalHomH1
import Dubon2026.RationalTraceFiniteLocalHomH1
import Dubon2026.ArithmeticFiniteSUnitLocalH1Map
import Dubon2026.ArithmeticTraceSUnitLocalH1Comparison

/-! The proved native finite S-unit H1 map agrees with localization through
the original trace-dual identification. This identifies the exact maps
used by DUB-17's direct finite-correction class, using their literal cocycles. -/
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

/-- The exact finite/global trace coefficient localization square. -/
abbrev RationalTraceFiniteSUnitLocalizationComparison : Prop :=
    ∀ x : RationalTraceFiniteSUnitHomH1 a ha q σ F hker,
    rationalTraceFiniteLocalHomH1Equiv a q σ F hker p hp hσ hn
      (arithmeticFiniteSUnitLocalH1Map a ha F (rationalTraceOriginalFiniteRep a q σ F hker) p hp x) =
    rationalTraceSUnitLocalH1Map a ha q σ hσ hqa hn p hp
      (rationalArithmeticTraceSUnitH1Equiv a ha q σ hσ hqa hn
        (rationalTraceFiniteSUnitHomH1Equiv a ha q σ F hker hσ hqa hn x))

/-- The actual finite S-unit localization and original trace localization
give the same prime-local continuous H1 class. -/
theorem rationalTraceFiniteSUnitLocalization_comparison :
    RationalTraceFiniteSUnitLocalizationComparison a ha q σ F hker hσ hqa hn p hp := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    have hc := rationalTraceFiniteSUnitHomH1Equiv_toHom_mk a ha q σ F hker hσ hqa hn c
    refine Eq.trans ?_ (congrArg (rationalTraceSUnitLocalH1Map a ha q σ hσ hqa hn p hp) hc).symm
    change rationalTraceFiniteLocalHomH1Equiv a q σ F hker p hp hσ hn
      (Submodule.Quotient.mk _) = rationalTraceSUnitLocalH1Map a ha q σ hσ hqa hn p hp
        (Submodule.Quotient.mk _)
    refine (rationalTraceFiniteLocalHomH1Equiv_mk a q σ F hker p hp hσ hn _).trans ?_
    refine Eq.trans ?_ (rationalTraceSUnitLocalH1Map_mk a ha q σ hσ hqa hn p hp _).symm
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    apply Subtype.ext
    funext g
    apply LinearMap.ext
    intro Y
    rfl

end
end Dubon2026
