import Dubon2026.MatrixOrdinaryRelationIdeal

/-! # The ordinary ideal cuts out the actual original invariant direct-summand condition -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G R A K : Type*} [Group G] [CommRing R]
  [CommRing A] [IsLocalRing A] [Field K]

/-- Killing the original ordinary relation ideal is equivalent to the genuine invariant submodule of the same coefficient-changed representation being a free rank-one direct summand. -/
theorem matrixOrdinaryRelationIdeal_le_kernel_iff_invariants
    (ρ : G →* GeneralLinearGroup (Fin 2) R) (g₀ : G)
    (f : R →+* A) (r : A →+* K) [IsLocalHom r]
    (hρ : GeneralLinearGroup.map (r.comp f) (ρ g₀) ≠ 1) :
    matrixOrdinaryRelationIdeal ρ g₀ ≤ RingHom.ker f ↔
      (Nonempty ((matrixStandardRepresentation ((GeneralLinearGroup.map f).comp ρ)).invariants
          ≃ₗ[A] A) ∧
        ∃ N : Submodule A (Fin 2 → A),
          IsCompl (matrixStandardRepresentation ((GeneralLinearGroup.map f).comp ρ)).invariants N) := by
  rw [matrixOrdinaryRelationIdeal_le_kernel_iff]
  apply matrixOrdinary_relations_iff_invariants_split r ((GeneralLinearGroup.map f).comp ρ) g₀
  exact hρ

end
end Dubon2026
