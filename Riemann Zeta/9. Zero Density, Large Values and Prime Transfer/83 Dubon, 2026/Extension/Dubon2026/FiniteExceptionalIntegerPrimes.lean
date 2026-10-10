import Mathlib.RingTheory.DedekindDomain.Factorization

/-! # Finiteness of the actual exceptional prime set of a nonzero integer -/

namespace Dubon2026

open IsDedekindDomain

/-- Only finitely many original height-one primes contain a given nonzero element of the original Dedekind domain. -/
theorem heightOnePrimes_containing_nonzero_finite
    {R : Type*} [CommRing R] [IsDedekindDomain R] (a : R) (ha : a ≠ 0) :
    {v : HeightOneSpectrum R | a ∈ v.asIdeal}.Finite := by
  have hI : (Ideal.span {a} : Ideal R) ≠ 0 := by
    simpa only [Ideal.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot] using ha
  simpa only [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem] using Ideal.finite_factors hI

end Dubon2026
