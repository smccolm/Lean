import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-! # Actual height-one primes above an original prime -/

namespace Dubon2026

open IsDedekindDomain

variable {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
  [Algebra R S] [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]

/-- Every original height-one prime has a genuine height-one prime above it in an integral extension of domains. -/
theorem heightOnePrime_exists_liesOver (v : HeightOneSpectrum R) :
    ∃ w : HeightOneSpectrum S, w.asIdeal.LiesOver v.asIdeal := by
  obtain ⟨P⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver S))
  letI : P.val.IsPrime := P.property.1
  letI : P.val.LiesOver v.asIdeal := P.property.2
  exact ⟨⟨P.val, P.property.1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P.val⟩,
    P.property.2⟩

end Dubon2026
