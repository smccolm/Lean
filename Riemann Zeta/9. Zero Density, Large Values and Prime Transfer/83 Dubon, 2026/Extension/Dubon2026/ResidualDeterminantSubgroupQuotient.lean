import Dubon2026.ResidualDeterminantQuotient
import Dubon2026.ResidualRelationQuotient
import Dubon2026.OriginalAdicLocalQuotientData

/-! # Genuine original local quotients imposing determinant and subgroup relations together -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι O R : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R]

/-- Original residual determinant compatibility and actual residual subgroup-killing make the literal sum of the two existing relation ideals a proper ideal, and its actual coefficient quotient a local ring. -/
theorem representationDeterminantSubgroupQuotient_isLocal
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup ι R)
    (σ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hρ : (GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom).comp ρ = σ)
    (δ : G →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (N : Subgroup G) (hN : N ≤ σ.ker) :
    IsLocalRing (R ⧸ (representationDeterminantIdeal ρ δ ⊔ matrixRepresentationRelationIdeal ρ N)) := by
  let J := representationDeterminantIdeal ρ δ ⊔ matrixRepresentationRelationIdeal ρ N
  have hJ : J ≤ IsLocalRing.maximalIdeal R := sup_le
    (representationDeterminantIdeal_le_maximal eR ρ σ hρ δ hδ)
    (matrixRepresentationRelationIdeal_le_maximal eR ρ σ hρ N hN)
  have hproper : J ≠ ⊤ := by
    intro ht
    rw [ht, top_le_iff] at hJ
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top hJ
  letI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hproper
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective

/-- The genuine original determinant-and-subgroup quotient has derived complete local Noetherian data in its own original quotient topology, using actual residual compatibility and original maximal-adic completeness. -/
theorem representationDeterminantSubgroupQuotient_localData
    [IsNoetherianRing R] [Finite (IsLocalRing.ResidueField O)]
    [TopologicalSpace R] [IsTopologicalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (hR : IsAdic (IsLocalRing.maximalIdeal R))
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup ι R)
    (σ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hρ : (GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom).comp ρ = σ)
    (δ : G →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (N : Subgroup G) (hN : N ≤ σ.ker) :
    let J := representationDeterminantIdeal ρ δ ⊔ matrixRepresentationRelationIdeal ρ N
    letI := representationDeterminantSubgroupQuotient_isLocal eR ρ σ hρ δ hδ N hN
    IsNoetherianRing (R ⧸ J) ∧ IsAdic (IsLocalRing.maximalIdeal (R ⧸ J)) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal (R ⧸ J)) (R ⧸ J) := by
  letI : Finite (IsLocalRing.ResidueField R) := Finite.of_injective eR eR.injective
  letI := representationDeterminantSubgroupQuotient_isLocal eR ρ σ hρ δ hδ N hN
  exact originalAdicLocalQuotient_localData hR
    (representationDeterminantIdeal ρ δ ⊔ matrixRepresentationRelationIdeal ρ N)

end
end Dubon2026
