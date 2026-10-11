import Dubon2026.ResidualDeterminantQuotient
import Dubon2026.OriginalResidualHopfModel
import Dubon2026.MatrixHopfModelCoefficientQuotientLocalData

/-! # The actual complete local quotient imposing determinant and finite-flat conditions -/

namespace Dubon2026
noncomputable section
open Matrix
universe u

variable {R F K O A H ι : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [CommRing O] [IsLocalRing O] [CommRing A] [IsLocalRing A] [Algebra O A]
  [TopologicalSpace A] [IsTopologicalRing A] [Group H] [Fintype ι] [DecidableEq ι]

/-- Residual determinant compatibility and the genuine residual local model put both
original coefficient ideals in the original maximal ideal. Their actual sum quotient
is therefore a nontrivial local ring; locality is derived rather than assumed. -/
theorem representationDeterminantHopfFlatQuotient_isLocal
    (hA : IsAdic (IsLocalRing.maximalIdeal A))
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (τ : H →* GeneralLinearGroup ι A)
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eA).toRingHom).comp τ = σ)
    (δ : H →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (j : (K ≃ₐ[F] K) →* H)
    (m : FiniteFreeHopfPointModel.{u,u,u,u,u} R F K
      (Multiplicative (ι → IsLocalRing.ResidueField O))
      (matrixUnderlyingGroupAction (σ.comp j))) :
    IsLocalRing (A ⧸ (representationDeterminantIdeal τ δ ⊔
      matrixHopfModelCoefficientIdeal R F K (τ.comp j))) := by
  let mA := originalResidualHopfModel eA τ σ hτ j m
  have hopen : IsOpen (IsLocalRing.maximalIdeal A : Set A) := by
    simpa using (isAdic_iff.mp hA).1 1
  let J := representationDeterminantIdeal τ δ ⊔
    matrixHopfModelCoefficientIdeal R F K (τ.comp j)
  have hJ : J ≤ IsLocalRing.maximalIdeal A := sup_le
    (representationDeterminantIdeal_le_maximal eA τ σ hτ δ hδ)
    (matrixHopfModelCoefficientIdeal_le_maximal (τ.comp j) hopen mA)
  have hproper : J ≠ ⊤ := by
    intro ht
    rw [ht, top_le_iff] at hJ
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top hJ
  letI : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hproper
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective

/-- The same sum quotient has its actual Noetherian, complete maximal-adic local
structure, using the original residue field and quotient topology. -/
theorem representationDeterminantHopfFlatQuotient_localData
    [IsNoetherianRing A] [Finite (IsLocalRing.ResidueField O)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hA : IsAdic (IsLocalRing.maximalIdeal A))
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (τ : H →* GeneralLinearGroup ι A)
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eA).toRingHom).comp τ = σ)
    (δ : H →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (j : (K ≃ₐ[F] K) →* H)
    (m : FiniteFreeHopfPointModel.{u,u,u,u,u} R F K
      (Multiplicative (ι → IsLocalRing.ResidueField O))
      (matrixUnderlyingGroupAction (σ.comp j))) :
    let J := representationDeterminantIdeal τ δ ⊔
      matrixHopfModelCoefficientIdeal R F K (τ.comp j)
    letI := representationDeterminantHopfFlatQuotient_isLocal hA eA τ σ hτ δ hδ j m
    IsNoetherianRing (A ⧸ J) ∧ IsAdic (IsLocalRing.maximalIdeal (A ⧸ J)) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal (A ⧸ J)) (A ⧸ J) := by
  letI : Finite (IsLocalRing.ResidueField A) := Finite.of_injective eA eA.injective
  letI := representationDeterminantHopfFlatQuotient_isLocal hA eA τ σ hτ δ hδ j m
  exact originalAdicLocalQuotient_localData hA
    (representationDeterminantIdeal τ δ ⊔ matrixHopfModelCoefficientIdeal R F K (τ.comp j))

end
end Dubon2026
