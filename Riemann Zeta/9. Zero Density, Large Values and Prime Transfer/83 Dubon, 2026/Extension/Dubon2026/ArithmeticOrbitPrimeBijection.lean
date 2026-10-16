import Dubon2026.ArithmeticOrbitPrimeIndex
import Dubon2026.ArithmeticOrbitPrimeSurjectivity

/-! # Actual local Mackey orbits are exactly the original primes above p

Combine the proved original-prime fiber calculation with surjectivity
through a finite normal cover. The map is the same literal induced-prime
map on the exact orbit quotient used by the Mackey formula. This closes
the indexing input for DUB-17's number-field reciprocity transfer; the
global localization invariant and total sum still require assembly.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]

/-- The exact Mackey orbit index reaches every genuine original prime above p. -/
theorem rationalArithmeticOrbitPrimeIndex_surjective :
    Function.Surjective (rationalArithmeticOrbitPrimeIndex a p hp F) := by
  rintro ⟨w, hw⟩
  obtain ⟨c, hc⟩ := rationalArithmeticOrbitPrime_surjective a p hp F w hw
  exact ⟨Quotient.mk'' c, Subtype.ext hc⟩

/-- The exact local Mackey orbit quotient is equivalent to all genuine original primes above p. -/
def rationalArithmeticOrbitPrimeEquiv :
    cosetOrbitIndex (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
      (rationalArithmeticOrbitFixingSubgroup a F) ≃
        {w : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // originalIntegerPrimeBelow F w = rationalPrimePlace p hp} :=
  Equiv.ofBijective (rationalArithmeticOrbitPrimeIndex a p hp F)
    ⟨rationalArithmeticOrbitPrimeIndex_injective a p hp F,
      rationalArithmeticOrbitPrimeIndex_surjective a p hp F⟩

/-- The original-prime equivalence retains the literal induced prime of every actual coset. -/
theorem rationalArithmeticOrbitPrimeEquiv_mk
    (c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F) :
    (rationalArithmeticOrbitPrimeEquiv a p hp F (Quotient.mk'' c)).val =
      rationalArithmeticOrbitPrime a p hp F c := rfl

/-- The exact orbit representative in the Mackey formula has precisely the prime selected by the equivalence. -/
theorem rationalArithmeticOrbitPrimeEquiv_out
    (ω : cosetOrbitIndex (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
      (rationalArithmeticOrbitFixingSubgroup a F)) :
    (rationalArithmeticOrbitPrimeEquiv a p hp F ω).val =
      rationalArithmeticOrbitPrime a p hp F ω.out := by
  conv_lhs => rw [← Quotient.out_eq' ω]
  rfl

end
end Dubon2026
