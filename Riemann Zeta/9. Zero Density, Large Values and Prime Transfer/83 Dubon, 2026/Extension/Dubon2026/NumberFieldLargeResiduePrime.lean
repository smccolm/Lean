import Dubon2026.HeightOnePrimeLifting
import Dubon2026.RationalPrimePlace
import Dubon2026.OriginalAdicCompletionResidue
import Mathlib.Data.Nat.Prime.Infinite

/-! # Large original residue primes for arithmetic small levels

Euclid's theorem and the existing original lying-over and residue
comparison theorems supply the size condition in DUB-17's constructed
principal level, avoiding any specified finite list of rational primes.
The source's additional splitting and unramified conditions remain separate.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain
open scoped NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- The actual completion residue field has the characteristic of its original prime below. -/
theorem originalAdicResidue_charP_of_prime_mem
    (v : HeightOneSpectrum (𝓞 K)) (p : ℕ) (hp : p.Prime)
    (hmem : (p : 𝓞 K) ∈ v.asIdeal) :
    CharP (Valued.ResidueField (v.adicCompletion K)) p := by
  apply (CharP.charP_iff_prime_eq_zero hp).mpr
  have hz : (p : 𝓞 K ⧸ v.asIdeal) = 0 := by
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  have h := congrArg (originalRingOfIntegersQuotientEquivAdicResidueField K v) hz
  simpa using h

/-- An original finite place of sufficiently large residue characteristic exists outside any finite list. -/
theorem numberField_exists_large_residue_prime (B : ℕ) (T : Finset ℕ) :
    ∃ (v : HeightOneSpectrum (𝓞 K)) (p : ℕ), p.Prime ∧ B < p - 1 ∧ p ∉ T ∧
      CharP (Valued.ResidueField (v.adicCompletion K)) p := by
  obtain ⟨p, hbound, hp⟩ := Nat.exists_infinite_primes (max B (T.sup id) + 2)
  obtain ⟨v, hv⟩ := heightOnePrime_exists_liesOver (S := 𝓞 K) (rationalPrimePlace p hp)
  letI : v.asIdeal.LiesOver (rationalPrimePlace p hp).asIdeal := hv
  have hmem : (p : 𝓞 K) ∈ v.asIdeal := by
    simpa using (Ideal.mem_of_liesOver v.asIdeal (rationalPrimePlace p hp).asIdeal (p : ℤ)).mp
      ((rationalPrimePlace_nat_mem_iff p hp p).mpr (dvd_refl p))
  refine ⟨v, p, hp, ?_, ?_, originalAdicResidue_charP_of_prime_mem K v p hp hmem⟩
  · have := le_max_left B (T.sup id)
    omega
  · intro h
    have hle : p ≤ T.sup id := Finset.le_sup (f := id) h
    have := le_max_right B (T.sup id)
    omega

end
end Dubon2026
