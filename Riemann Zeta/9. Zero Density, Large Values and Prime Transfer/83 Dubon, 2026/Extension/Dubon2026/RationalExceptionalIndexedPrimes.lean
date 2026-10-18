import Dubon2026.RationalOriginalExceptionalPrimeFamily

/-! The original exceptional rational-prime index supplies the actual
lower and upper primes directly. This feeds DUB-17's indexed Cartier
relation construction while retaining each literal completion parameter. -/
namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField Classical
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitCompletionNumberField
  rationalArithmeticOriginalPrimeLiesOver

variable (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- The original number-field prime attached to the given exceptional rational prime. -/
abbrev rationalExceptionalIndexedBasePrime (p : rationalArithmeticExceptionalPrimes a ha) :
    HeightOneSpectrum (𝓞 ℚ) := rationalOriginalPrimePlace p.val.val p.val.property

/-- Different original exceptional rational primes give different actual base primes. -/
theorem rationalExceptionalIndexedBasePrime_injective :
    Function.Injective (rationalExceptionalIndexedBasePrime a ha) := by
  intro p q h
  exact Subtype.ext (rationalOriginalPrimePlace_injective h)

variable (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))

/-- The original embedding-selected upper prime belongs to the actual S-unit support. -/
abbrev rationalExceptionalIndexedUpperPrime (p : rationalArithmeticExceptionalPrimes a ha) :
    originalExceptionalIntegerSupport F (algebraMap (𝓞 ℚ) (𝓞 F) a)
      (originalIntegerMap_ne_zero (L := F) a ha) :=
  ⟨rationalArithmeticOriginalPrime a p.val.val p.val.property F,
    (rationalArithmeticOriginalPrime_mem_exceptional_support a ha p.val F).mpr p.property⟩

/-- The original selected upper prime lies over the literal prime at its original index. -/
local instance rationalExceptionalIndexedPrimeLiesOver (p : rationalArithmeticExceptionalPrimes a ha) :
    (rationalExceptionalIndexedUpperPrime a ha F p).val.asIdeal.LiesOver
      (rationalExceptionalIndexedBasePrime a ha p).asIdeal :=
  inferInstanceAs ((rationalArithmeticOriginalPrime a p.val.val p.val.property F).asIdeal.LiesOver
    (rationalOriginalPrimePlace p.val.val p.val.property).asIdeal)

/-- Actual contraction of the selected upper prime recovers the specified base prime. -/
theorem rationalExceptionalIndexedUpperPrime_below (p : rationalArithmeticExceptionalPrimes a ha) :
    originalFinitePrimeBelow ℚ F (rationalExceptionalIndexedUpperPrime a ha F p).val =
      rationalExceptionalIndexedBasePrime a ha p :=
  originalFinitePrimeBelow_eq_of_liesOver ℚ F (rationalExceptionalIndexedBasePrime a ha p)
    (rationalExceptionalIndexedUpperPrime a ha F p).val

end
end Dubon2026
