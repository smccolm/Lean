import Dubon2026.LocalIntegralResiduePrime
import Dubon2026.RationalArithmeticFrobeniusLift

/-! Identify the contracted residue prime above the original rational
prime. This discharges the prime-identification input for DUB-17's
comparison of actual local inertia with the selected unramified finite
factor. The norm inequality will be supplied by the original completion. -/

namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField

variable {F L : Type} [Field F] [NormedField L] [IsUltrametricDist L]
  (e : F →+* L) (p : ℕ) (hp : p.Prime) (hnorm : ‖(p : L)‖ < 1)

include hnorm in
/-- The original rational prime maps to zero in the actual local residue field. -/
theorem algebraicLocalGlobalPrime_prime_mem :
    (p : 𝓞 F) ∈ algebraicLocalGlobalPrime e := by
  change IsLocalRing.residue (algebraicLocalIntegerRing L)
    (algebraicLocalGlobalIntegerMap e (p : 𝓞 F)) = 0
  rw [map_natCast, IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
  change ‖(p : L)‖₊ < 1
  exact_mod_cast hnorm

variable [NumberField F]
include hp hnorm

/-- The contracted prime is nonzero in the original number-field integer ring. -/
theorem algebraicLocalGlobalPrime_ne_bot : algebraicLocalGlobalPrime e ≠ ⊥ := by
  intro he
  have hm := algebraicLocalGlobalPrime_prime_mem e p hnorm
  rw [he, Ideal.mem_bot] at hm
  exact (Nat.cast_ne_zero.mpr hp.ne_zero) hm

/-- The contracted prime lies over the same original rational prime ideal. -/
theorem algebraicLocalGlobalPrime_under :
    (algebraicLocalGlobalPrime e).under (𝓞 ℚ) = (rationalOriginalPrimePlace p hp).asIdeal := by
  letI : (algebraicLocalGlobalPrime e).IsPrime := algebraicLocalGlobalPrime_isPrime e
  have hle : (rationalOriginalPrimePlace p hp).asIdeal ≤
      (algebraicLocalGlobalPrime e).under (𝓞 ℚ) := by
    rw [rationalOriginalPrimePlace_eq_span]
    rw [Ideal.span_le, Set.singleton_subset_iff]
    change algebraMap (𝓞 ℚ) (𝓞 F) (p : 𝓞 ℚ) ∈ algebraicLocalGlobalPrime e
    rw [map_natCast]
    exact algebraicLocalGlobalPrime_prime_mem e p hnorm
  exact ((rationalOriginalPrimePlace p hp).isMaximal.eq_of_le
    (Ideal.IsPrime.ne_top inferInstance) hle).symm

end
end Dubon2026
