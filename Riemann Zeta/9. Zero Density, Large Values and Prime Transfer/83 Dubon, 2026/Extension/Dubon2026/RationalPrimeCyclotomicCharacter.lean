import Dubon2026.PrimitiveRootCyclotomicContinuity
import Dubon2026.RationalPrimeArithmeticRestriction
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # The genuine finite cyclotomic character at the actual rational prime completion -/

namespace Dubon2026
noncomputable section

/-- The actual local absolute Galois group acts on primitive roots by this
continuous finite cyclotomic character. The roots exist in its original algebraic
closure; their existence and continuity are derived. -/
def rationalPrimeCyclotomicCharacter (p : ℕ) (hp : p.Prime) (n : ℕ) [NeZero n] :
    (rationalPrimeLocalClosure p hp ≃ₐ[rationalPrimeLocalField p hp]
      rationalPrimeLocalClosure p hp) →ₜ* (ZMod n)ˣ := by
  letI : CharZero (rationalPrimeLocalField p hp) :=
    Algebra.charZero_of_charZero (R := ℚ) (A := rationalPrimeLocalField p hp)
  have hx := HasEnoughRootsOfUnity.exists_primitiveRoot (rationalPrimeLocalClosure p hp) n
  have hμ := Classical.choose_spec hx
  exact ⟨hμ.autToPow (rationalPrimeLocalField p hp),
    primitiveRootCyclotomicCharacter_continuous hμ⟩

/-- The constructed character gives the literal exponent action on every
primitive root in the original prime-local algebraic closure. -/
theorem rationalPrimeCyclotomicCharacter_apply_root
    (p : ℕ) (hp : p.Prime) (n : ℕ) [NeZero n]
    (g : rationalPrimeLocalClosure p hp ≃ₐ[rationalPrimeLocalField p hp]
      rationalPrimeLocalClosure p hp)
    {ζ : rationalPrimeLocalClosure p hp} (hζ : IsPrimitiveRoot ζ n) :
    g ζ = ζ ^ (rationalPrimeCyclotomicCharacter p hp n g : ZMod n).val := by
  letI : CharZero (rationalPrimeLocalField p hp) :=
    Algebra.charZero_of_charZero (R := ℚ) (A := rationalPrimeLocalField p hp)
  have hx := HasEnoughRootsOfUnity.exists_primitiveRoot (rationalPrimeLocalClosure p hp) n
  exact primitiveRootCyclotomicCharacter_apply_root
    (F := rationalPrimeLocalField p hp) (Classical.choose_spec hx) g hζ

end
end Dubon2026
