import Dubon2026.OriginalLocalEmbeddingPrime
import Dubon2026.LocalFieldAlgHomValuationComparison
import Dubon2026.OriginalFinitePrimeOrbits

/-! # Induced original primes contract along the literal global field tower

This comparison lets the prime-surjectivity proof descend from a finite
Galois cover to the arbitrary original finite field required by DUB-17.
All prime ideals are the original maximal-ideal pullbacks; the local-field
embedding preserves their strict integrality by the proved integral-closure
valuation comparison.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField ValuativeRel

variable (L H E M : Type) [Field L] [NumberField L] [Field H] [NumberField H]
  [Algebra L H] [Field E] [Field M] [Algebra L E] [Algebra H M]
  (p : ℕ) (hp : p.Prime)
  [Algebra (rationalPrimeLocalField p hp) E] [Algebra (rationalPrimeLocalField p hp) M]
  [ValuativeRel E] [ValuativeRel M] [TopologicalSpace E] [TopologicalSpace M]
  [IsNonarchimedeanLocalField E] [IsNonarchimedeanLocalField M]
  [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension (ValuativeRel.valuation E)]
  [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension (ValuativeRel.valuation M)]

/-- The genuine prime induced on the upper field contracts to the prime induced by the compatible lower local embedding. -/
theorem originalLocalEmbeddingPrime_under_eq
    (e : E →ₐ[rationalPrimeLocalField p hp] M)
    (he : ∀ x : L, e (algebraMap L E x) = algebraMap H M (algebraMap L H x)) :
    originalFinitePrimeBelow L H (originalLocalEmbeddingPrime H M p hp) =
      originalLocalEmbeddingPrime L E p hp := by
  apply IsDedekindDomain.HeightOneSpectrum.ext
  apply Ideal.ext
  intro x
  change algebraMap (𝓞 L) (𝓞 H) x ∈ (originalLocalEmbeddingPrime H M p hp).asIdeal ↔
    x ∈ (originalLocalEmbeddingPrime L E p hp).asIdeal
  rw [originalLocalEmbeddingPrime_mem_iff, originalLocalEmbeddingPrime_mem_iff]
  change ValuativeRel.valuation M (algebraMap H M (algebraMap L H (x : L))) < 1 ↔ _
  rw [← he]
  exact localFieldAlgHom_valuation_lt_one_iff (rationalPrimeLocalField p hp) E M e (algebraMap L E (x : L))

end
end Dubon2026
