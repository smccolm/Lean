import Dubon2026.OriginalLocalEmbeddingPrime
import Dubon2026.LocalFieldAlgHomValuationComparison
import Dubon2026.NumberFieldGaloisPlaces

/-! # Literal global twisting of induced original primes

A local embedding that intertwines an original global automorphism
transports the induced original prime by exactly that automorphism.
This is the equivariance input for DUB-17's prime-surjectivity argument
through a finite Galois cover; no prime-transitivity conclusion is assumed.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField ValuativeRel

variable (L E M : Type) [Field L] [NumberField L] [Field E] [Field M]
  [Algebra L E] [Algebra L M] (p : ℕ) (hp : p.Prime)
  [Algebra (rationalPrimeLocalField p hp) E] [Algebra (rationalPrimeLocalField p hp) M]
  [ValuativeRel E] [ValuativeRel M] [TopologicalSpace E] [TopologicalSpace M]
  [IsNonarchimedeanLocalField E] [IsNonarchimedeanLocalField M]
  [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension (ValuativeRel.valuation E)]
  [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension (ValuativeRel.valuation M)]

/-- The actual global automorphism transports the original induced primes when their literal local embeddings intertwine it. -/
theorem originalLocalEmbeddingPrime_galoisComparison
    (e : E →ₐ[rationalPrimeLocalField p hp] M) (σ : Gal(L/ℚ))
    (he : ∀ x : L, e (algebraMap L E x) = algebraMap L M (σ x)) :
    numberFieldGaloisPlaceEquiv ℚ L σ (originalLocalEmbeddingPrime L E p hp) =
      originalLocalEmbeddingPrime L M p hp := by
  apply IsDedekindDomain.HeightOneSpectrum.ext
  apply Ideal.ext
  intro x
  change NumberField.RingOfIntegers.mapRingHom σ.symm.toRingHom x ∈
    (originalLocalEmbeddingPrime L E p hp).asIdeal ↔ x ∈ (originalLocalEmbeddingPrime L M p hp).asIdeal
  rw [originalLocalEmbeddingPrime_mem_iff, originalLocalEmbeddingPrime_mem_iff]
  change ValuativeRel.valuation E (algebraMap L E (σ.symm (x : L))) < 1 ↔ _
  have h := localFieldAlgHom_valuation_lt_one_iff (rationalPrimeLocalField p hp) E M e
    (algebraMap L E (σ.symm (x : L)))
  rw [he, σ.apply_symm_apply] at h
  exact h.symm

end
end Dubon2026
