import Dubon2026.MatrixRepresentationRelationIdeals
import Dubon2026.LocalCoefficientReduction
import Dubon2026.LocalQuotientCoefficientFibers

/-! # Genuine local quotients imposing original residual-compatible subgroup relations -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι O R : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R]

/-- If the original residual representation kills the original subgroup, its actual relation ideal lies in the true coefficient maximal ideal. -/
theorem matrixRepresentationRelationIdeal_le_maximal
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup ι R)
    (σ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hρ : (GeneralLinearGroup.map (n := ι) (localCoefficientReduction eR).toRingHom).comp ρ = σ)
    (N : Subgroup G) (hN : N ≤ σ.ker) :
    matrixRepresentationRelationIdeal ρ N ≤ IsLocalRing.maximalIdeal R := by
  have hker := (matrixRepresentationRelationIdeal_le_kernel_iff ρ N
    (localCoefficientReduction eR).toRingHom).mpr (by rw [hρ]; exact hN)
  intro r hr
  exact (localCoefficientReduction_eq_zero_iff eR r).mp (hker hr)

/-- Imposing the actual original subgroup relations gives a genuine nontrivial local coefficient quotient when those relations hold in the original residual representation. -/
theorem matrixRepresentationRelationQuotient_isLocal
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup ι R)
    (σ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hρ : (GeneralLinearGroup.map (n := ι) (localCoefficientReduction eR).toRingHom).comp ρ = σ)
    (N : Subgroup G) (hN : N ≤ σ.ker) :
    IsLocalRing (R ⧸ matrixRepresentationRelationIdeal ρ N) := by
  have hproper : matrixRepresentationRelationIdeal ρ N ≠ ⊤ := by
    intro ht
    have hm := matrixRepresentationRelationIdeal_le_maximal eR ρ σ hρ N hN
    rw [ht, top_le_iff] at hm
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top hm
  letI : Nontrivial (R ⧸ matrixRepresentationRelationIdeal ρ N) :=
    Ideal.Quotient.nontrivial_iff.mpr hproper
  exact IsLocalRing.of_surjective'
    (Ideal.Quotient.mk (matrixRepresentationRelationIdeal ρ N)) Ideal.Quotient.mk_surjective

end
end Dubon2026
