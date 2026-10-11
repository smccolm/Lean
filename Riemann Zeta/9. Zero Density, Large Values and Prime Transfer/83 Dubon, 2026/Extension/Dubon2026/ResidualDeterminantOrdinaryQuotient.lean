import Dubon2026.ResidualDeterminantQuotient
import Dubon2026.ResidualOrdinaryRelationQuotient

/-! # The original complete local quotient imposing determinant and ordinarity simultaneously -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G O R : Type*} [Group G] [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R]

/-- Original residual determinant compatibility and actual residual ordinarity place the sum of the genuine determinant and ordinary ideals in the maximal ideal, deriving locality of the literal combined quotient. -/
theorem representationDeterminantOrdinaryQuotient_isLocal
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup (Fin 2) R)
    (σ : G →* GeneralLinearGroup (Fin 2) (IsLocalRing.ResidueField O))
    (hρ : (GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom).comp ρ = σ)
    (δ : G →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (N : Subgroup G) (g₀ : N) (hg₀ : σ g₀.val ≠ 1)
    (hOrd : Nonempty ((matrixStandardRepresentation (σ.comp N.subtype)).invariants
        ≃ₗ[IsLocalRing.ResidueField O] IsLocalRing.ResidueField O) ∧
      ∃ W : Submodule (IsLocalRing.ResidueField O) (Fin 2 → IsLocalRing.ResidueField O),
        IsCompl (matrixStandardRepresentation (σ.comp N.subtype)).invariants W) :
    IsLocalRing (R ⧸ (representationDeterminantIdeal ρ δ ⊔
      matrixOrdinaryRelationIdeal (ρ.comp N.subtype) g₀)) := by
  have hρN : (GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom).comp
      (ρ.comp N.subtype) = σ.comp N.subtype := by
    apply MonoidHom.ext
    intro g
    exact DFunLike.congr_fun hρ g.val
  let J := representationDeterminantIdeal ρ δ ⊔ matrixOrdinaryRelationIdeal (ρ.comp N.subtype) g₀
  have hJ : J ≤ IsLocalRing.maximalIdeal R := sup_le
    (representationDeterminantIdeal_le_maximal eR ρ σ hρ δ hδ)
    (matrixOrdinaryRelationIdeal_le_maximal eR (ρ.comp N.subtype) (σ.comp N.subtype)
      hρN g₀ hg₀ hOrd)
  have hproper : J ≠ ⊤ := by
    intro ht
    rw [ht, top_le_iff] at hJ
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top hJ
  letI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hproper
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective

/-- The genuine combined determinant and ordinary coefficient quotient has derived Noetherianity, its own maximal-adic topology and completeness. -/
theorem representationDeterminantOrdinaryQuotient_localData
    [IsNoetherianRing R] [Finite (IsLocalRing.ResidueField O)]
    [TopologicalSpace R] [IsTopologicalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (hR : IsAdic (IsLocalRing.maximalIdeal R))
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup (Fin 2) R)
    (σ : G →* GeneralLinearGroup (Fin 2) (IsLocalRing.ResidueField O))
    (hρ : (GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom).comp ρ = σ)
    (δ : G →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (N : Subgroup G) (g₀ : N) (hg₀ : σ g₀.val ≠ 1)
    (hOrd : Nonempty ((matrixStandardRepresentation (σ.comp N.subtype)).invariants
        ≃ₗ[IsLocalRing.ResidueField O] IsLocalRing.ResidueField O) ∧
      ∃ W : Submodule (IsLocalRing.ResidueField O) (Fin 2 → IsLocalRing.ResidueField O),
        IsCompl (matrixStandardRepresentation (σ.comp N.subtype)).invariants W) :
    let J := representationDeterminantIdeal ρ δ ⊔ matrixOrdinaryRelationIdeal (ρ.comp N.subtype) g₀
    letI := representationDeterminantOrdinaryQuotient_isLocal eR ρ σ hρ δ hδ N g₀ hg₀ hOrd
    IsNoetherianRing (R ⧸ J) ∧ IsAdic (IsLocalRing.maximalIdeal (R ⧸ J)) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal (R ⧸ J)) (R ⧸ J) := by
  letI : Finite (IsLocalRing.ResidueField R) := Finite.of_injective eR eR.injective
  letI := representationDeterminantOrdinaryQuotient_isLocal eR ρ σ hρ δ hδ N g₀ hg₀ hOrd
  exact originalAdicLocalQuotient_localData hR
    (representationDeterminantIdeal ρ δ ⊔ matrixOrdinaryRelationIdeal (ρ.comp N.subtype) g₀)

end
end Dubon2026
