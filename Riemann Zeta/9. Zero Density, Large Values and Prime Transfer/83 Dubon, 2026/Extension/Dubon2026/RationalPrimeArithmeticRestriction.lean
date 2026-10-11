import Dubon2026.RationalPrimePlace
import Dubon2026.RationalArithmeticLocalRestrictionContinuity
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-! # The actual prime completion and its continuous arithmetic restriction

Reuse the original rational prime place already constructed in this project.
The local field and integer ring are its genuine adic completion objects.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField

/-- The genuine completion of the original rational field at its original prime place. -/
abbrev rationalPrimeLocalField (p : ℕ) (hp : p.Prime) :=
  (rationalPrimePlace p hp).adicCompletion ℚ

/-- The original valuation integer ring in the same actual prime completion. -/
abbrev rationalPrimeLocalIntegerRing (p : ℕ) (hp : p.Prime) :=
  (rationalPrimePlace p hp).adicCompletionIntegers ℚ

/-- The actual algebraic closure of that same original prime completion. -/
abbrev rationalPrimeLocalClosure (p : ℕ) (hp : p.Prime) :=
  AlgebraicClosure (rationalPrimeLocalField p hp)

/-- The original prime-completion integer ring has the actual domain, PID and
fraction-field structures required by the finite-flat model constructions.
These are inherited from the pinned original completion objects. -/
theorem rationalPrimeLocalIntegerRing_properties (p : ℕ) (hp : p.Prime) :
    IsDomain (rationalPrimeLocalIntegerRing p hp) ∧
      IsPrincipalIdealRing (rationalPrimeLocalIntegerRing p hp) ∧
      IsFractionRing (rationalPrimeLocalIntegerRing p hp) (rationalPrimeLocalField p hp) := by
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- The actual local absolute Galois group at the original prime maps continuously
to the existing rational arithmetic Galois group through the constructed embedding
of its original extension into this same prime-completion algebraic closure. -/
def rationalPrimeArithmeticRestriction (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime) :
    (rationalPrimeLocalClosure p hp ≃ₐ[rationalPrimeLocalField p hp]
      rationalPrimeLocalClosure p hp) →ₜ* rationalArithmeticGaloisGroup a :=
  rationalArithmeticLocalRestrictionContinuous a

/-- The actual prime-local restriction keeps the exact original field-element
action under the same chosen rational embedding into the actual local closure. -/
theorem rationalPrimeArithmeticRestriction_commutes
    (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
    (g : rationalPrimeLocalClosure p hp ≃ₐ[rationalPrimeLocalField p hp]
      rationalPrimeLocalClosure p hp) (x : rationalUnramifiedExtension a) :
    let U := rationalUnramifiedExtension a
    letI : Algebra ℚ U := U.algebra'
    rationalArithmeticLocalEmbedding (K := rationalPrimeLocalClosure p hp) a
        ((show U ≃ₐ[ℚ] U from rationalPrimeArithmeticRestriction a p hp g) x) =
      g (rationalArithmeticLocalEmbedding (K := rationalPrimeLocalClosure p hp) a x) := by
  exact rationalArithmeticLocalRestrictionContinuous_commutes a g x

end
end Dubon2026
