import Dubon2026.ArithmeticCyclotomicH2UnramifiedRestriction
import Dubon2026.RationalExceptionalPrimeFinite

/-! # Finite support of the original arithmetic cyclotomic H2 restrictions

The support consists of actual primes and the actual original local H2 maps.
It is contained in the proved finite set dividing the exceptional integer.
This removes the finite-prime support assumption from the DUB-17 route to the
global invariant sum; the reciprocity identity itself remains separate.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField

variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)

/-- The nonzero original prime-local restrictions of every original arithmetic
cyclotomic H2 class form a finite set, derived from actual unramified vanishing. -/
theorem rationalArithmeticCyclotomicH2_finite_support (ha : a ≠ 0)
    (x : ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous)) :
    {p : Nat.Primes | rationalPrimeCyclotomicH2Restriction a q hqa p.val p.property x ≠ 0}.Finite := by
  apply (rationalExceptionalPrimeSet_finite a ha).subset
  intro p hp
  by_contra hpa
  exact hp (rationalPrimeCyclotomicH2Restriction_eq_zero a q hqa p.val p.property ha hpa x)

end
end Dubon2026
