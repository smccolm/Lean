import Dubon2026.RepresentationDeterminantIdeal
import Dubon2026.LocalCoefficientReduction
import Dubon2026.LocalQuotientCoefficientFibers

/-! # The genuine local coefficient quotient with prescribed residual-compatible determinant -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι O R : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R]

/-- A prescribed determinant compatible with the original residual matrices gives an ideal inside the actual coefficient maximal ideal. -/
theorem representationDeterminantIdeal_le_maximal
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup ι R)
    (σ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hρ : (GeneralLinearGroup.map (n := ι) (localCoefficientReduction eR).toRingHom).comp ρ = σ)
    (δ : G →* Oˣ)
    (hδ : ∀ g : G, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g)) :
    representationDeterminantIdeal ρ δ ≤ IsLocalRing.maximalIdeal R := by
  have hker := (representationDeterminantIdeal_le_kernel_iff ρ δ
    (localCoefficientReduction eR)).mpr (fun g => by
      rw [show GeneralLinearGroup.map (n := ι) (localCoefficientReduction eR).toRingHom
        (ρ g) = σ g from DFunLike.congr_fun hρ g]
      exact hδ g)
  intro r hr
  exact (localCoefficientReduction_eq_zero_iff eR r).mp (hker hr)

/-- The original residual-compatible determinant quotient is a genuine nontrivial local ring. -/
theorem representationDeterminantQuotient_isLocal
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup ι R)
    (σ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hρ : (GeneralLinearGroup.map (n := ι) (localCoefficientReduction eR).toRingHom).comp ρ = σ)
    (δ : G →* Oˣ)
    (hδ : ∀ g : G, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g)) :
    IsLocalRing (R ⧸ representationDeterminantIdeal ρ δ) := by
  have hproper : representationDeterminantIdeal ρ δ ≠ ⊤ := by
    intro ht
    have hm := representationDeterminantIdeal_le_maximal eR ρ σ hρ δ hδ
    rw [ht, top_le_iff] at hm
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top hm
  letI : Nontrivial (R ⧸ representationDeterminantIdeal ρ δ) :=
    Ideal.Quotient.nontrivial_iff.mpr hproper
  exact IsLocalRing.of_surjective'
    (Ideal.Quotient.mk (representationDeterminantIdeal ρ δ)) Ideal.Quotient.mk_surjective

/-- The true residue field of the actual fixed-determinant quotient is the original specified coefficient residue field. -/
def representationDeterminantQuotientResidueEquiv
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup ι R) (δ : G →* Oˣ)
    [IsLocalRing (R ⧸ representationDeterminantIdeal ρ δ)] :
    IsLocalRing.ResidueField (R ⧸ representationDeterminantIdeal ρ δ) ≃ₐ[O]
      IsLocalRing.ResidueField O :=
  originalLocalQuotientResidueEquiv eR (representationDeterminantIdeal ρ δ)

/-- The actual determinant quotient retains the original reduction of every coefficient. -/
theorem representationDeterminantQuotientResidueEquiv_original
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup ι R) (δ : G →* Oˣ)
    [IsLocalRing (R ⧸ representationDeterminantIdeal ρ δ)] (r : R) :
    localCoefficientReduction (representationDeterminantQuotientResidueEquiv eR ρ δ)
      (Ideal.Quotient.mk (representationDeterminantIdeal ρ δ) r) = localCoefficientReduction eR r :=
  originalLocalQuotientResidueEquiv_original eR (representationDeterminantIdeal ρ δ) r

end
end Dubon2026
