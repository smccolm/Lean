import Dubon2026.LocalFieldArithmeticFrobeniusUniqueness

/-! # Powers of actual local arithmetic Frobenius on original residues -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]

/-- Each actual power of arithmetic Frobenius has the corresponding
iterated cardinality-power action on the original residue representatives. -/
theorem localFieldArithmeticFrobenius_pow_residue (n : ℕ) (x : 𝒪[L]) :
    IsLocalRing.residue 𝒪[L]
      (localFieldIntegerGaloisEquiv K L (localFieldArithmeticFrobenius K L ^ n) x) =
        IsLocalRing.residue 𝒪[L] x ^ (Nat.card 𝓀[K] ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', map_mul, AlgEquiv.mul_apply,
      localFieldArithmeticFrobenius_residue, ih, ← pow_mul, ← pow_succ]

/-- The actual residue action determines the corresponding power of
the original arithmetic Frobenius. -/
theorem localFieldArithmeticFrobenius_eq_pow_of_residue (g : Gal(L/K)) (n : ℕ)
    (hg : ∀ x : 𝒪[L], IsLocalRing.residue 𝒪[L] (localFieldIntegerGaloisEquiv K L g x) =
      IsLocalRing.residue 𝒪[L] x ^ (Nat.card 𝓀[K] ^ n)) :
    g = localFieldArithmeticFrobenius K L ^ n := by
  apply (localFieldIntegerGaloisEquiv K L).injective
  letI := IsTopologicalAddGroup.rightUniformSpace L
  haveI := isUniformAddGroup_of_addCommGroup (G := L)
  apply unramifiedSeparated_algEquiv_eq_of_residue
  intro x
  exact (hg x).trans (localFieldArithmeticFrobenius_pow_residue K L n x).symm

end
end Dubon2026
