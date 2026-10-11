import Dubon2026.MatrixOrdinaryRelationIdeal
import Dubon2026.LocalCoefficientReduction
import Dubon2026.OriginalAdicLocalQuotientData

/-! # Residual ordinary data makes the literal ordinary relation quotient a complete local ring -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G O R : Type*} [Group G] [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R]

/-- When the genuine residual invariant module is a free rank-one direct summand, every actual ordinary relation lies in the original coefficient maximal ideal. -/
theorem matrixOrdinaryRelationIdeal_le_maximal
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup (Fin 2) R)
    (σ : G →* GeneralLinearGroup (Fin 2) (IsLocalRing.ResidueField O))
    (hρ : (GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom).comp ρ = σ)
    (g₀ : G) (hg₀ : σ g₀ ≠ 1)
    (hOrd : Nonempty ((matrixStandardRepresentation σ).invariants ≃ₗ[IsLocalRing.ResidueField O]
        IsLocalRing.ResidueField O) ∧
      ∃ N : Submodule (IsLocalRing.ResidueField O) (Fin 2 → IsLocalRing.ResidueField O),
        IsCompl (matrixStandardRepresentation σ).invariants N) :
    matrixOrdinaryRelationIdeal ρ g₀ ≤ IsLocalRing.maximalIdeal R := by
  have hrel := (matrixOrdinary_relations_iff_invariants_split
    (RingHom.id (IsLocalRing.ResidueField O)) σ g₀ hg₀).mpr hOrd
  have hker := (matrixOrdinaryRelationIdeal_le_kernel_iff ρ g₀
    (localCoefficientReduction eR).toRingHom).mpr (by rw [hρ]; exact hrel)
  intro x hx
  exact (localCoefficientReduction_eq_zero_iff eR x).mp (hker hx)

/-- The actual ordinary coefficient quotient is a nontrivial local ring, derived from the original residual ordinary invariant module. -/
theorem matrixOrdinaryRelationQuotient_isLocal
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup (Fin 2) R)
    (σ : G →* GeneralLinearGroup (Fin 2) (IsLocalRing.ResidueField O))
    (hρ : (GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom).comp ρ = σ)
    (g₀ : G) (hg₀ : σ g₀ ≠ 1)
    (hOrd : Nonempty ((matrixStandardRepresentation σ).invariants ≃ₗ[IsLocalRing.ResidueField O]
        IsLocalRing.ResidueField O) ∧
      ∃ N : Submodule (IsLocalRing.ResidueField O) (Fin 2 → IsLocalRing.ResidueField O),
        IsCompl (matrixStandardRepresentation σ).invariants N) :
    IsLocalRing (R ⧸ matrixOrdinaryRelationIdeal ρ g₀) := by
  have hproper : matrixOrdinaryRelationIdeal ρ g₀ ≠ ⊤ := by
    intro ht
    have hm := matrixOrdinaryRelationIdeal_le_maximal eR ρ σ hρ g₀ hg₀ hOrd
    rw [ht, top_le_iff] at hm
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top hm
  letI : Nontrivial (R ⧸ matrixOrdinaryRelationIdeal ρ g₀) :=
    Ideal.Quotient.nontrivial_iff.mpr hproper
  exact IsLocalRing.of_surjective'
    (Ideal.Quotient.mk (matrixOrdinaryRelationIdeal ρ g₀)) Ideal.Quotient.mk_surjective

/-- The original ordinary relation quotient has its own complete Noetherian maximal-adic structure, derived from the genuine residual ordinary condition. -/
theorem matrixOrdinaryRelationQuotient_localData
    [IsNoetherianRing R] [Finite (IsLocalRing.ResidueField O)]
    [TopologicalSpace R] [IsTopologicalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (hR : IsAdic (IsLocalRing.maximalIdeal R))
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup (Fin 2) R)
    (σ : G →* GeneralLinearGroup (Fin 2) (IsLocalRing.ResidueField O))
    (hρ : (GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom).comp ρ = σ)
    (g₀ : G) (hg₀ : σ g₀ ≠ 1)
    (hOrd : Nonempty ((matrixStandardRepresentation σ).invariants ≃ₗ[IsLocalRing.ResidueField O]
        IsLocalRing.ResidueField O) ∧
      ∃ N : Submodule (IsLocalRing.ResidueField O) (Fin 2 → IsLocalRing.ResidueField O),
        IsCompl (matrixStandardRepresentation σ).invariants N) :
    let J := matrixOrdinaryRelationIdeal ρ g₀
    letI := matrixOrdinaryRelationQuotient_isLocal eR ρ σ hρ g₀ hg₀ hOrd
    IsNoetherianRing (R ⧸ J) ∧ IsAdic (IsLocalRing.maximalIdeal (R ⧸ J)) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal (R ⧸ J)) (R ⧸ J) := by
  letI : Finite (IsLocalRing.ResidueField R) := Finite.of_injective eR eR.injective
  letI := matrixOrdinaryRelationQuotient_isLocal eR ρ σ hρ g₀ hg₀ hOrd
  exact originalAdicLocalQuotient_localData hR (matrixOrdinaryRelationIdeal ρ g₀)

end
end Dubon2026
