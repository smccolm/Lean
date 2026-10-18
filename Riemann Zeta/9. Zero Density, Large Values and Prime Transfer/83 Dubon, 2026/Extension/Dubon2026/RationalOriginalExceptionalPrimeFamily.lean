import Dubon2026.RationalOriginalExceptionalSupport
import Dubon2026.OriginalFullIdeleInvariantPrimeSupport

/-! The actual exceptional rational-prime family supplies the distinct
base primes and original embedding-selected upper primes required by the
finite relation construction. This retains all original local inputs in
DUB-17's arithmetic Cartier cup sum, with no support or lifting premise. -/
namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField Classical
attribute [local instance] arithmeticOrbitCompletionNumberField rationalArithmeticOriginalPrimeLiesOver

variable (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- The original exceptional primes, indexed in the rational number
field's ring of integers for the original completion construction. -/
def rationalOriginalExceptionalPrimeSet : Finset (HeightOneSpectrum (𝓞 ℚ)) :=
  (rationalArithmeticExceptionalPrimes a ha).image
    (fun p => rationalOriginalPrimePlace p.val p.property)

/-- The original exceptional rational primes index exactly the same
finite family after the proved injective number-field-prime comparison. -/
def rationalOriginalExceptionalPrimeIndex :
    (rationalArithmeticExceptionalPrimes a ha) ≃ (rationalOriginalExceptionalPrimeSet a ha) :=
  Equiv.ofBijective
    (fun p => ⟨rationalOriginalPrimePlace p.val.val p.val.property,
      Finset.mem_image.mpr ⟨p.val, p.property, rfl⟩⟩)
    ⟨fun p q h => Subtype.ext (rationalOriginalPrimePlace_injective (congrArg Subtype.val h)),
      fun v => by
        obtain ⟨p, hp, he⟩ := Finset.mem_image.mp v.property
        exact ⟨⟨p, hp⟩, Subtype.ext he⟩⟩

/-- The inverse indexing retains the literal original base prime. -/
theorem rationalOriginalExceptionalPrimeIndex_symm_prime
    (v : rationalOriginalExceptionalPrimeSet a ha) :
    rationalOriginalPrimePlace ((rationalOriginalExceptionalPrimeIndex a ha).symm v).val.val
      ((rationalOriginalExceptionalPrimeIndex a ha).symm v).val.property = v.val :=
  congrArg Subtype.val ((rationalOriginalExceptionalPrimeIndex a ha).apply_symm_apply v)

variable (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))

/-- Select the original arithmetic embedding prime above each original
exceptional base prime, deriving membership in the actual S-unit support. -/
def rationalOriginalExceptionalUpperPrime
    (v : rationalOriginalExceptionalPrimeSet a ha) :
    originalExceptionalIntegerSupport F (algebraMap (𝓞 ℚ) (𝓞 F) a)
      (originalIntegerMap_ne_zero (L := F) a ha) :=
  let p := (rationalOriginalExceptionalPrimeIndex a ha).symm v
  ⟨rationalArithmeticOriginalPrime a p.val.val p.val.property F,
    (rationalArithmeticOriginalPrime_mem_exceptional_support a ha p.val F).mpr p.property⟩

/-- Every selected upper prime contracts to its specified original base
prime, exactly as required by the finite local relation-family theorem. -/
theorem rationalOriginalExceptionalUpperPrime_below
    (v : rationalOriginalExceptionalPrimeSet a ha) :
    originalFinitePrimeBelow ℚ F (rationalOriginalExceptionalUpperPrime a ha F v).val = v.val := by
  let p := (rationalOriginalExceptionalPrimeIndex a ha).symm v
  exact (originalFinitePrimeBelow_eq_of_liesOver ℚ F
    (rationalOriginalPrimePlace p.val.val p.val.property)
    (rationalArithmeticOriginalPrime a p.val.val p.val.property F)).trans
      (rationalOriginalExceptionalPrimeIndex_symm_prime a ha v)

end
end Dubon2026
