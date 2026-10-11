import Dubon2026.LocalFieldIntegerGaloisTower
import Dubon2026.LocalFieldArithmeticFrobeniusUniqueness

/-! # Actual arithmetic Frobenius commutes with original unramified field restriction -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [IsGalois K L] [IsGalois K M]
  [ValuativeRel K] [ValuativeRel L] [ValuativeRel M]
  [TopologicalSpace K] [TopologicalSpace L] [TopologicalSpace M]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [IsNonarchimedeanLocalField M]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [(ValuativeRel.valuation L).HasExtension (ValuativeRel.valuation M)]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation M)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[M]]

/-- Restriction of the genuine upper arithmetic Frobenius is precisely
the genuine lower arithmetic Frobenius. Actual integer and residue inclusions
and the original cardinality-power characterization prove the equality. -/
theorem localFieldArithmeticFrobenius_restrict :
    AlgEquiv.restrictNormalHom L (localFieldArithmeticFrobenius K M) =
      localFieldArithmeticFrobenius K L := by
  apply localFieldArithmeticFrobenius_eq_of_residue
  intro x
  apply (algebraMap 𝓀[L] 𝓀[M]).injective
  rw [IsLocalRing.ResidueField.algebraMap_residue, map_pow,
    IsLocalRing.ResidueField.algebraMap_residue,
    localFieldIntegerGaloisEquiv_restrict]
  exact localFieldArithmeticFrobenius_residue K M (algebraMap 𝒪[L] 𝒪[M] x)

end
end Dubon2026
