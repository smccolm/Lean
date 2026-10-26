import Dubon2026.OriginalLocalEmbeddingPrime

/-! DUB-17/18 -> all-weight residual association -> choose the local
coefficient place from the source's prescribed algebraic-integer reduction.
Its actual kernel is a nonzero prime above the prescribed rational prime;
no place or compatibility certificate is supplied. -/
namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField
variable (F : Type) [Field F] [NumberField F]
variable {k : Type*} [Field k] (ell : ℕ) (hell : ell.Prime) [CharP k ell]

/-- The genuine Fourier-integer prime given by the kernel of the prescribed reduction. -/
def sourceReductionPrime (φ : 𝓞 F →+* k) : HeightOneSpectrum (𝓞 F) where
  asIdeal := RingHom.ker φ
  isPrime := RingHom.ker_isPrime φ
  ne_bot := by
    intro h
    have hm : (ell : 𝓞 F) ∈ RingHom.ker φ := by
      change φ (ell : 𝓞 F) = 0
      rw [map_natCast, CharP.cast_eq_zero]
    rw [h, Ideal.mem_bot] at hm
    exact (Nat.cast_ne_zero.mpr hell.ne_zero) hm

theorem sourceReductionPrime_prime_mem (φ : 𝓞 F →+* k) :
    (ell : 𝓞 F) ∈ (sourceReductionPrime F ell hell φ).asIdeal := by
  change φ (ell : 𝓞 F) = 0
  rw [map_natCast, CharP.cast_eq_zero]

theorem sourceReductionPrime_below (φ : 𝓞 F →+* k) :
    originalIntegerPrimeBelow F (sourceReductionPrime F ell hell φ) =
      rationalPrimePlace ell hell := by
  by_contra h
  apply rationalPrimePlace_prime_not_mem ell hell _ h
  change algebraMap ℤ (𝓞 F) (ell : ℤ) ∈ (sourceReductionPrime F ell hell φ).asIdeal
  simpa only [map_natCast] using sourceReductionPrime_prime_mem F ell hell φ

end
end Dubon2026
