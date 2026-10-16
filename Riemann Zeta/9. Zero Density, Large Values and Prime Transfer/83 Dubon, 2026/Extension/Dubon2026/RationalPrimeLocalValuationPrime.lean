import Dubon2026.RationalPrimeLocalizedIntegerUnits

/-! # The original rational prime has strictly positive local valuation

This identifies a nonzero element in the prime pulled back from an
arithmetic orbit field. It is the first prime-indexing input still needed
for DUB-17's comparison with individual number-field completions.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped ValuativeRel WithZero

/-- The original rational prime lies strictly inside the maximal ideal
of its original completion's canonical valuation ring. -/
theorem rationalPrimeLocal_valuation_prime_lt_one (p : ℕ) (hp : p.Prime) :
    ValuativeRel.valuation (rationalPrimeLocalField p hp) (p : rationalPrimeLocalField p hp) < 1 := by
  rw [← (ValuativeRel.valuation (rationalPrimeLocalField p hp)).vlt_one_iff,
    (Valued.v (R := rationalPrimeLocalField p hp) (Γ₀ := ℤᵐ⁰)).vlt_one_iff]
  rw [← map_natCast (algebraMap ℚ (rationalPrimeLocalField p hp)) p,
    algebraMap_adicCompletion, Function.comp_apply, Valued.valuedCompletion_apply]
  change (rationalPrimePlace p hp).valuation ℚ (algebraMap ℤ ℚ (p : ℤ)) < 1
  rw [valuation_of_algebraMap, intValuation_lt_one_iff_mem]
  exact (rationalPrimePlace_nat_mem_iff p hp p).mpr (dvd_refl p)

end
end Dubon2026
