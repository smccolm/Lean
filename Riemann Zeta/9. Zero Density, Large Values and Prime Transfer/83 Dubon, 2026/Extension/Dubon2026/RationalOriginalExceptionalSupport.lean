import Dubon2026.RationalArithmeticOriginalCompletionTower
import Dubon2026.ArithmeticExceptionalTraceDuality
import Dubon2026.ArithmeticExceptionalSUnitSupport

/-! Identify the exceptional primes used by the original trace pairing
with the actual number-field primes needed by the finite relation family.
This supplies the support and distinct-base-prime inputs for DUB-17's
canonical local cup sum, using the unchanged exceptional integer. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] arithmeticOrbitCompletionNumberField rationalArithmeticOriginalPrimeLiesOver

/-- Containment of the original exceptional integer at the original
rational number-field prime is exactly the original divisibility condition. -/
theorem rationalOriginalPrimePlace_mem_iff (p : ℕ) (hp : p.Prime) (a : 𝓞 ℚ) :
    a ∈ (rationalOriginalPrimePlace p hp).asIdeal ↔ (p : 𝓞 ℚ) ∣ a := by
  let e := Rat.ringOfIntegersEquiv
  have hz : ((e a : ℤ) : 𝓞 ℚ) = a :=
    (map_intCast e.symm (e a)).symm.trans (e.symm_apply_apply a)
  have hm : a ∈ (rationalOriginalPrimePlace p hp).asIdeal ↔
      e a ∈ (originalIntegerPrimeBelow ℚ (rationalOriginalPrimePlace p hp)).asIdeal := by
    change a ∈ (rationalOriginalPrimePlace p hp).asIdeal ↔
      ((e a : ℤ) : 𝓞 ℚ) ∈ (rationalOriginalPrimePlace p hp).asIdeal
    rw [hz]
  rw [rationalOriginalPrimePlace_below, rationalPrimePlace_int_mem_iff] at hm
  refine hm.trans ⟨fun hd => ?_, fun hd => ?_⟩
  · have h := map_dvd e.symm.toRingHom hd
    simpa only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, map_natCast, e.symm_apply_apply] using h
  · have h := map_dvd e.toRingHom hd
    simpa only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, map_natCast] using h

/-- Distinct original rational primes remain distinct in the
ring-of-integers prime family used by the original completion maps. -/
theorem rationalOriginalPrimePlace_injective :
    Function.Injective (fun p : Nat.Primes => rationalOriginalPrimePlace p.val p.property) := by
  intro p q h
  apply Subtype.ext
  have hb := congrArg (originalIntegerPrimeBelow ℚ) h
  rw [rationalOriginalPrimePlace_below, rationalOriginalPrimePlace_below] at hb
  have hn := congrArg Rat.HeightOneSpectrum.natGenerator hb
  simpa only [rationalPrimePlace_natGenerator] using hn

/-- The actual arithmetic prime selected by the original local embedding
belongs to the same original finite S-unit support exactly at the primes
in the original exceptional trace-pairing family. -/
theorem rationalArithmeticOriginalPrime_mem_exceptional_support
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : Nat.Primes)
    (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a)) :
    rationalArithmeticOriginalPrime a p.val p.property F ∈
      originalExceptionalIntegerSupport F (algebraMap (𝓞 ℚ) (𝓞 F) a)
        (originalIntegerMap_ne_zero (L := F) a ha) ↔
      p ∈ rationalArithmeticExceptionalPrimes a ha := by
  rw [mem_originalExceptionalIntegerSupport, mem_rationalArithmeticExceptionalPrimes]
  exact ((rationalArithmeticOriginalPrime a p.val p.property F).asIdeal.mem_of_liesOver
    (rationalOriginalPrimePlace p.val p.property).asIdeal a).symm.trans
      (rationalOriginalPrimePlace_mem_iff p.val p.property a)

end
end Dubon2026
