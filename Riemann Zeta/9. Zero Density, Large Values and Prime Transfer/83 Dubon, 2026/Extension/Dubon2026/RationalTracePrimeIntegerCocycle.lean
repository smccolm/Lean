import Dubon2026.RationalPrimeTraceIntegerCocycle
import Dubon2026.RationalTraceOriginalLocalAction
import Dubon2026.RationalPrimeTraceIntegerCohomology
import Dubon2026.ContinuousTraceZeroRestriction

/-! Retain the original source trace-zero cocycle under prime restriction
and conversion to integer coefficients. This is the literal representative
consumed by DUB-17's original-completion Cartier cup comparison. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance 1100] Rep.hV1 Rep.hV2 Submodule.module
attribute [local instance] primeTraceIntegerContinuousSMul

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime]
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
  (p : ℕ) (hp : p.Prime)

/-- The original source cocycle is restricted at the actual prime and
viewed over the integers by the existing additive coefficient equivalence. -/
def rationalTracePrimeIntegerCocycle (c : continuousTraceZeroAdjointCocycles σ) :
    continuousRepresentationCocyclesOne (rationalPrimeTraceZeroIntegerRep p hp q
      (σ.comp (rationalPrimeArithmeticRestriction a p hp))) :=
  rationalPrimeTraceIntegerCocycle p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp))
    (continuousTraceZeroAdjointRestriction σ (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
      (rationalPrimeArithmeticRestriction a p hp).continuous c)

/-- The restricted integer cocycle has exactly the original matrix value. -/
theorem rationalTracePrimeIntegerCocycle_apply (c : continuousTraceZeroAdjointCocycles σ)
    (g : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp)) :
    (rationalTracePrimeIntegerCocycle a q σ p hp c).val g =
      c.val (rationalPrimeArithmeticRestriction a p hp g) := rfl

/-- Its integer H1 class is the original trace-zero H1 restriction,
through the existing coefficient equivalence and unchanged quotient. -/
theorem rationalTracePrimeIntegerCocycle_class (hσ : Continuous σ)
    (c : continuousTraceZeroAdjointCocycles σ) :
    rationalPrimeTraceIntegerH1Equiv p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp))
      (hσ.comp (rationalPrimeArithmeticRestriction a p hp).continuous)
      (continuousTraceZeroH1Restriction σ hσ (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
        (rationalPrimeArithmeticRestriction a p hp).continuous (Quotient.mk _ c)) =
      Quotient.mk _ (rationalTracePrimeIntegerCocycle a q σ p hp c) := rfl

end
end Dubon2026
