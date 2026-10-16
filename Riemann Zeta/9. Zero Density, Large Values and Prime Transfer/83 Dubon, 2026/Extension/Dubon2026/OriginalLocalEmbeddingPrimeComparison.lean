import Dubon2026.OriginalLocalEmbeddingPrime
import Dubon2026.LocalFieldIntegerAlgEquiv

/-! # Induced original primes under literal local-field comparisons

The existing integral-closure theorem identifies original integer rings
under a local-base equivalence. Their maximal ideals then have the same
pullback on the actual global integers. This is the representative
independence input in DUB-17's original-prime indexing of Mackey summands.
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

/-- A literal local-base equivalence preserving the global embedding preserves its actual induced prime. -/
theorem originalLocalEmbeddingPrime_eq_of_algEquiv
    (e : E ≃ₐ[rationalPrimeLocalField p hp] M)
    (he : ∀ x : L, e (algebraMap L E x) = algebraMap L M x) :
    originalLocalEmbeddingPrime L E p hp = originalLocalEmbeddingPrime L M p hp := by
  let j := localFieldIntegerAlgEquiv (rationalPrimeLocalField p hp) E M e
  apply IsDedekindDomain.HeightOneSpectrum.ext
  apply Ideal.ext
  intro x
  have hj : j (originalIntegerToValuationIntegerMap L E x) =
      originalIntegerToValuationIntegerMap L M x := by
    apply Subtype.ext
    exact (localFieldIntegerAlgEquiv_coefficient (rationalPrimeLocalField p hp) E M e
      (originalIntegerToValuationIntegerMap L E x)).trans (he x)
  change originalIntegerToValuationIntegerMap L E x ∈ IsLocalRing.maximalIdeal 𝒪[E] ↔
    originalIntegerToValuationIntegerMap L M x ∈ IsLocalRing.maximalIdeal 𝒪[M]
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, mem_nonunits_iff, ← hj]
  exact not_congr (MulEquiv.isUnit_map j).symm

end
end Dubon2026
