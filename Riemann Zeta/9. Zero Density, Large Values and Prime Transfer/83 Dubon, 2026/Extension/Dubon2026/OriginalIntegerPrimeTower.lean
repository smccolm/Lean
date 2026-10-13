import Dubon2026.OriginalUnramifiedIntegerUniformizer
import Dubon2026.OriginalFinitePrimeOrbits
import Mathlib.RingTheory.Ideal.NatInt

/-! # Integer primes below the original common-extension primes

Literal contraction in a tower identifies the rational primes under the
original localization support and the cyclotomic completion. These facts
discharge the indexing premise when applying the constructed local-degree
stage to the actual global H2 class on DUB-17's sum-zero route.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField

/-- The actual integer prime below an original finite place is unchanged by contraction in the original number-field tower. -/
theorem originalIntegerPrimeBelow_tower
    (L M : Type) [Field L] [NumberField L] [Field M] [NumberField M] [Algebra L M]
    (t : HeightOneSpectrum (𝓞 M)) :
    originalIntegerPrimeBelow L (originalFinitePrimeBelow L M t) = originalIntegerPrimeBelow M t := by
  apply HeightOneSpectrum.ext
  exact Ideal.under_under t.asIdeal

/-- Every original finite place lies over a genuine positive rational prime. -/
theorem originalIntegerPrimeBelow_exists_prime
    (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) :
    ∃ p : ℕ, p.Prime ∧ w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
  rcases Ideal.isPrime_int_iff.mp (originalIntegerPrimeBelow L w).isPrime with hz | ⟨p, hp, he⟩
  · exact False.elim ((originalIntegerPrimeBelow L w).ne_bot hz)
  · refine ⟨p, hp, ?_⟩
    rw [← he]
    exact ⟨rfl⟩

end
end Dubon2026
