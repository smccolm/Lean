import Dubon2026.ArithmeticTraceSUnitLocalHom
import Dubon2026.ArithmeticCyclotomicCohomologyRestriction
import Dubon2026.RationalPrimeTraceUnitCocycle
import Dubon2026.RationalTraceCoherentSourceCup

/-! Retain the exact cocycle in the normalized original local trace-dual
H1 class. This isolates the actual target computation in DUB-17's S-unit
localization square without changing its original coefficient objects. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance 1100] Rep.hV1 Rep.hV2 Submodule.addCommGroup Submodule.module
attribute [local instance] primeTraceUnitHomContinuousSMul
  exceptionalTraceRootTopology exceptionalTraceRootDiscrete
  exceptionalTraceUnitTopology exceptionalTraceUnitDiscrete

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime]
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
  (hσ : Continuous σ) (hqa : (q : 𝓞 ℚ) ∣ a)
  (hn : (Fintype.card ι : ZMod q) ≠ 0) (p : ℕ) (hp : p.Prime)
  [TopologicalSpace (rationalPrimeTraceUnitHomRep p hp q
    (σ.comp (rationalPrimeArithmeticRestriction a p hp)))]
  [DiscreteTopology (rationalPrimeTraceUnitHomRep p hp q
    (σ.comp (rationalPrimeArithmeticRestriction a p hp)))]

/-- The normalized original local H1 class retains the restricted
original cocycle, its derived coordinate factor and the native unit dual. -/
theorem rationalTraceLocalH1Target_mk
    (c : continuousRepresentationCocyclesOne (matrixTraceZeroCharacterRep σ
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)) :
    rationalPrimeTraceUnitH1Equiv p hp q
      (σ.comp (rationalPrimeArithmeticRestriction a p hp))
      (hσ.comp (rationalPrimeArithmeticRestriction a p hp).continuous) hn
      (rationalArithmeticLocalNormalizationScalar a q hqa p hp •
        rationalPrimeCyclotomicAdjointH1Restriction a q hqa p hp σ hσ (Submodule.Quotient.mk c)) =
    Submodule.Quotient.mk
      (rationalPrimeTraceUnitCocycleEquiv p hp q
        (σ.comp (rationalPrimeArithmeticRestriction a p hp)) hn
        (rationalTraceCoherentCartierSourceCocycle a q hqa σ p hp
          (continuousCocycleOneCoefficientCongr
            (rationalArithmeticTraceZeroCyclotomicTwist_restriction a q hqa σ p hp)
            (continuousRepresentationCocycleOneRestriction
              (matrixTraceZeroCharacterRep σ
                (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
              (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
              (rationalPrimeArithmeticRestriction a p hp).continuous c)))) := by
  exact congrArg (fun z => rationalPrimeTraceUnitH1Equiv p hp q
    (σ.comp (rationalPrimeArithmeticRestriction a p hp))
    (hσ.comp (rationalPrimeArithmeticRestriction a p hp).continuous) hn
    (rationalArithmeticLocalNormalizationScalar a q hqa p hp • z))
    (rationalPrimeCyclotomicAdjointH1Restriction_mk a q hqa p hp σ hσ c)

end
end Dubon2026
