import Dubon2026.RationalPrimeLocalValuationPrime
import Dubon2026.OriginalUnramifiedIntegerUniformizer
import Mathlib.RingTheory.Valuation.Extension

/-! # The actual number-field prime induced by a local embedding

Pull back the maximal ideal of the actual local valuation ring along
the original integer embedding. The rational prime is a nonzero member,
so this is a genuine finite prime. This begins the missing prime indexing
of the orbit fields in DUB-17's number-field reciprocity comparison.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField ValuativeRel

variable (L E : Type) [Field L] [NumberField L] [Field E] [Algebra L E]
  (p : ℕ) (hp : p.Prime) [Algebra (rationalPrimeLocalField p hp) E]
  [ValuativeRel E]
  [hExt : (ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension (ValuativeRel.valuation E)]

include hp hExt in
omit [NumberField L] in
private theorem originalLocalEmbeddingPrimeIdeal_prime_mem :
    (p : 𝓞 L) ∈ (IsLocalRing.maximalIdeal 𝒪[E]).comap (originalIntegerToValuationIntegerMap L E) := by
  change originalIntegerToValuationIntegerMap L E (p : 𝓞 L) ∈ IsLocalRing.maximalIdeal 𝒪[E]
  rw [map_natCast, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  change ValuativeRel.valuation E (p : E) < 1
  rw [← map_natCast (algebraMap (rationalPrimeLocalField p hp) E) p]
  exact (Valuation.HasExtension.val_map_lt_one_iff
    (ValuativeRel.valuation (rationalPrimeLocalField p hp)) (ValuativeRel.valuation E) _).mpr
    (rationalPrimeLocal_valuation_prime_lt_one p hp)

/-- The genuine finite number-field prime induced by the original local integer embedding. -/
def originalLocalEmbeddingPrime : HeightOneSpectrum (𝓞 L) where
  asIdeal := (IsLocalRing.maximalIdeal 𝒪[E]).comap (originalIntegerToValuationIntegerMap L E)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    have hm := originalLocalEmbeddingPrimeIdeal_prime_mem L E p hp
    rw [h, Ideal.mem_bot] at hm
    exact (Nat.cast_ne_zero.mpr hp.ne_zero) hm

/-- Membership in the actual induced finite prime is precisely strict
integrality under the literal original local embedding. -/
theorem originalLocalEmbeddingPrime_mem_iff (x : 𝓞 L) :
    x ∈ (originalLocalEmbeddingPrime L E p hp).asIdeal ↔
      ValuativeRel.valuation E (algebraMap L E (x : L)) < 1 := by
  change originalIntegerToValuationIntegerMap L E x ∈ IsLocalRing.maximalIdeal 𝒪[E] ↔ _
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  rfl

/-- The original rational prime belongs to the actual induced number-field prime. -/
theorem originalLocalEmbeddingPrime_prime_mem :
    (p : 𝓞 L) ∈ (originalLocalEmbeddingPrime L E p hp).asIdeal :=
  originalLocalEmbeddingPrimeIdeal_prime_mem L E p hp

/-- The genuine induced number-field prime lies over precisely the
original rational prime, through the existing integer-prime map. -/
theorem originalLocalEmbeddingPrime_below :
    originalIntegerPrimeBelow L (originalLocalEmbeddingPrime L E p hp) = rationalPrimePlace p hp := by
  let w := originalLocalEmbeddingPrime L E p hp
  have hm : (p : ℤ) ∈ (originalIntegerPrimeBelow L w).asIdeal := by
    change algebraMap ℤ (𝓞 L) (p : ℤ) ∈ w.asIdeal
    simpa only [map_natCast] using originalLocalEmbeddingPrime_prime_mem L E p hp
  have hd := (finitePlace_nat_mem_iff (originalIntegerPrimeBelow L w) p).mp hm
  have he : Rat.HeightOneSpectrum.natGenerator (originalIntegerPrimeBelow L w) = p :=
    (Nat.dvd_prime hp).mp hd |>.resolve_left
      (Rat.HeightOneSpectrum.prime_natGenerator (originalIntegerPrimeBelow L w)).ne_one
  apply Rat.HeightOneSpectrum.primesEquiv.injective
  apply Subtype.ext
  exact he.trans (rationalPrimePlace_natGenerator p hp).symm

end
end Dubon2026
