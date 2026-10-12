import Dubon2026.GaloisUnitBaseChange
import Dubon2026.LocalFieldArithmeticFrobeniusPowers

/-! # Original arithmetic Frobenius under actual finite base change -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable (K E L M : Type) [Field K] [Field E] [Field L] [Field M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M] [Normal K L]
  [ValuativeRel K] [ValuativeRel E] [ValuativeRel L] [ValuativeRel M]
  [TopologicalSpace K] [TopologicalSpace E] [TopologicalSpace L] [TopologicalSpace M]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField E]
  [IsNonarchimedeanLocalField L] [IsNonarchimedeanLocalField M]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [(ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation M)]
  [(ValuativeRel.valuation L).HasExtension (ValuativeRel.valuation M)]

omit [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)] in
/-- Actual change of base and original integer inclusions commute with
the literal original field automorphisms. -/
theorem localFieldIntegerGaloisEquiv_baseChange (g : Gal(M/E)) (x : 𝒪[L]) :
    algebraMap 𝒪[L] 𝒪[M]
      (localFieldIntegerGaloisEquiv K L (galoisBaseChangeRestriction K E L M g) x) =
        localFieldIntegerGaloisEquiv E M g (algebraMap 𝒪[L] 𝒪[M] x) := by
  apply FaithfulSMul.algebraMap_injective 𝒪[M] M
  change algebraMap L M (algebraMap 𝒪[L] L
    (localFieldIntegerGaloisEquiv K L (galoisBaseChangeRestriction K E L M g) x)) =
      algebraMap 𝒪[M] M (localFieldIntegerGaloisEquiv E M g (algebraMap 𝒪[L] 𝒪[M] x))
  rw [localFieldIntegerGaloisEquiv_apply, localFieldIntegerGaloisEquiv_apply]
  exact galoisBaseChangeRestriction_commutes K E L M g (algebraMap 𝒪[L] L x)

variable [IsGalois K L] [IsGalois E M]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]
  [Algebra.FormallyUnramified 𝒪[E] 𝒪[M]]

/-- The original upper arithmetic Frobenius restricts to the original
lower Frobenius raised to the actual residue degree of E over K. The base
extension may be ramified. -/
theorem localFieldArithmeticFrobenius_baseChange :
    galoisBaseChangeRestriction K E L M (localFieldArithmeticFrobenius E M) =
      localFieldArithmeticFrobenius K L ^ Module.finrank 𝓀[K] 𝓀[E] := by
  apply localFieldArithmeticFrobenius_eq_pow_of_residue K L
  intro x
  apply (algebraMap 𝓀[L] 𝓀[M]).injective
  rw [IsLocalRing.ResidueField.algebraMap_residue, map_pow,
    IsLocalRing.ResidueField.algebraMap_residue,
    localFieldIntegerGaloisEquiv_baseChange,
    localFieldArithmeticFrobenius_residue]
  rw [Module.natCard_eq_pow_finrank (K := 𝓀[K]) (V := 𝓀[E])]

end
end Dubon2026
