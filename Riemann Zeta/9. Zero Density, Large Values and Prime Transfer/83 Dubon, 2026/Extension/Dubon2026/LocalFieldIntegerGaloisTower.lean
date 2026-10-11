import Dubon2026.LocalFieldIntegerGaloisRestriction

/-! # Original integer-ring Galois actions commute with actual field restriction -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M] [Normal K L]
  [ValuativeRel K] [ValuativeRel L] [ValuativeRel M]
  [TopologicalSpace K] [TopologicalSpace L] [TopologicalSpace M]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [IsNonarchimedeanLocalField M]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [(ValuativeRel.valuation L).HasExtension (ValuativeRel.valuation M)]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation M)]

/-- Original field restriction and original integer inclusion commute on
the literal integer-ring elements. No compatibility certificate is assumed. -/
theorem localFieldIntegerGaloisEquiv_restrict (g : Gal(M/K)) (x : 𝒪[L]) :
    algebraMap 𝒪[L] 𝒪[M]
        (localFieldIntegerGaloisEquiv K L (AlgEquiv.restrictNormalHom L g) x) =
      localFieldIntegerGaloisEquiv K M g (algebraMap 𝒪[L] 𝒪[M] x) := by
  apply (FaithfulSMul.algebraMap_injective 𝒪[M] M)
  change algebraMap L M
      (algebraMap 𝒪[L] L
        (localFieldIntegerGaloisEquiv K L (AlgEquiv.restrictNormalHom L g) x)) =
    algebraMap 𝒪[M] M
      (localFieldIntegerGaloisEquiv K M g (algebraMap 𝒪[L] 𝒪[M] x))
  rw [localFieldIntegerGaloisEquiv_apply, localFieldIntegerGaloisEquiv_apply]
  exact AlgEquiv.restrictNormal_commutes g L (algebraMap 𝒪[L] L x)

end
end Dubon2026
