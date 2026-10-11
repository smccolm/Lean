import Dubon2026.UnramifiedLocalFieldResidueGalois
import Mathlib.FieldTheory.Finite.Basic

/-! # Actual arithmetic Frobenius in the original unramified local-field extension -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]

/-- The original arithmetic Frobenius is the unique original field
automorphism reducing to the cardinality power on the actual residue field. -/
def localFieldArithmeticFrobenius : Gal(L/K) := by
  letI : Fintype 𝓀[K] := Fintype.ofFinite _
  exact (unramifiedLocalFieldResidueGaloisEquiv K L).symm
    (FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[K] 𝓀[L])

/-- The original arithmetic Frobenius has precisely the actual residue
cardinality-power action, fixing its arithmetic rather than inverse convention. -/
theorem localFieldArithmeticFrobenius_residue (x : 𝒪[L]) :
    IsLocalRing.residue 𝒪[L]
      (localFieldIntegerGaloisEquiv K L (localFieldArithmeticFrobenius K L) x) =
        IsLocalRing.residue 𝒪[L] x ^ Nat.card 𝓀[K] := by
  letI : Fintype 𝓀[K] := Fintype.ofFinite _
  rw [← unramifiedLocalFieldResidueGaloisEquiv_apply]
  change ((unramifiedLocalFieldResidueGaloisEquiv K L)
    ((unramifiedLocalFieldResidueGaloisEquiv K L).symm
      (FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[K] 𝓀[L])))
        (IsLocalRing.residue 𝒪[L] x) = _
  rw [MulEquiv.apply_symm_apply]
  simp only [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, Nat.card_eq_fintype_card]

/-- Actual finite-field Frobenius generation transports through the genuine
residue equivalence to generate the original unramified local-field Galois group. -/
theorem localFieldArithmeticFrobenius_generates (g : Gal(L/K)) :
    g ∈ Subgroup.zpowers (localFieldArithmeticFrobenius K L) := by
  letI : Fintype 𝓀[K] := Fintype.ofFinite _
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow 𝓀[K] 𝓀[L]).2
    (unramifiedLocalFieldResidueGaloisEquiv K L g)
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨(n.val : ℤ), ?_⟩
  apply (unramifiedLocalFieldResidueGaloisEquiv K L).injective
  rw [map_zpow]
  change ((unramifiedLocalFieldResidueGaloisEquiv K L)
    ((unramifiedLocalFieldResidueGaloisEquiv K L).symm
      (FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[K] 𝓀[L]))) ^ (n.val : ℤ) = _
  rw [MulEquiv.apply_symm_apply, zpow_natCast]
  exact hn

end
end Dubon2026
