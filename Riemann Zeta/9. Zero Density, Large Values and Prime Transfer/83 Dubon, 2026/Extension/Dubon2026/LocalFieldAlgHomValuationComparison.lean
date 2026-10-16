import Dubon2026.LocalFieldValuativeExtensionUniqueness

/-! # Actual local embeddings preserve the valuation relation

The original integer rings are the integral closures of the common base
integer ring. Integrality is preserved and reflected by a field embedding.
This supplies the local comparison needed when contracting DUB-17's induced
primes from a finite Galois cover to an arbitrary finite arithmetic field.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel

variable (K E M : Type) [Field K] [Field E] [Field M]
  [Algebra K E] [Algebra K M]
  [ValuativeRel K] [ValuativeRel E] [ValuativeRel M]
  [TopologicalSpace K] [TopologicalSpace E] [TopologicalSpace M]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField E] [IsNonarchimedeanLocalField M]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation M)]

/-- The actual local-base embedding preserves and reflects the original valuation relation. -/
theorem localFieldAlgHom_valuation_isEquiv (f : E →ₐ[K] M) :
    (ValuativeRel.valuation E).IsEquiv ((ValuativeRel.valuation M).comap f.toRingHom) := by
  apply (Valuation.isEquiv_iff_valuationSubring _ _).mpr
  apply SetLike.ext
  intro x
  change ValuativeRel.valuation E x ≤ 1 ↔ ValuativeRel.valuation M (f x) ≤ 1
  rw [← Valuation.vle_one_iff, ← Valuation.vle_one_iff,
    localField_vle_one_iff_integral K E, localField_vle_one_iff_integral K M]
  exact (isIntegral_algHom_iff (f.restrictScalars 𝒪[K]) f.injective).symm

/-- Strict original integrality is preserved and reflected by the actual local embedding. -/
theorem localFieldAlgHom_valuation_lt_one_iff (f : E →ₐ[K] M) (x : E) :
    ValuativeRel.valuation M (f x) < 1 ↔ ValuativeRel.valuation E x < 1 := by
  have h := (localFieldAlgHom_valuation_isEquiv K E M f).lt_iff_lt (x := x) (y := (1 : E))
  simpa only [Valuation.comap_apply, map_one] using h.symm

end
end Dubon2026
