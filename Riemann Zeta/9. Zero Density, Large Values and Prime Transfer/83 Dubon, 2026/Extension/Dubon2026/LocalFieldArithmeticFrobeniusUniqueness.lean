import Dubon2026.LocalFieldArithmeticFrobenius

/-! # The actual residue characterization determines arithmetic Frobenius -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]

/-- The cardinality-power action on the actual residue representatives
characterizes the original arithmetic Frobenius. The residue action is
the action obtained from the original field automorphism. -/
theorem localFieldArithmeticFrobenius_eq_of_residue (g : Gal(L/K))
    (hg : ∀ x : 𝒪[L], IsLocalRing.residue 𝒪[L] (localFieldIntegerGaloisEquiv K L g x) =
      IsLocalRing.residue 𝒪[L] x ^ Nat.card 𝓀[K]) :
    g = localFieldArithmeticFrobenius K L := by
  apply (localFieldIntegerGaloisEquiv K L).injective
  letI := IsTopologicalAddGroup.rightUniformSpace L
  haveI := isUniformAddGroup_of_addCommGroup (G := L)
  apply unramifiedSeparated_algEquiv_eq_of_residue
  intro x
  exact (hg x).trans (localFieldArithmeticFrobenius_residue K L x).symm

end
end Dubon2026
