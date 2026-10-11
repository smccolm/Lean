import Dubon2026.MatrixIdealQuotientHopfModels
import Dubon2026.LocalCoefficientReduction

/-! # The genuine residual model gives the model of the original coefficient residue quotient -/

namespace Dubon2026
noncomputable section
open Matrix
universe u

variable {R F K ι O A H : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [Fintype ι] [DecidableEq ι] [CommRing O] [IsLocalRing O]
  [CommRing A] [IsLocalRing A] [Algebra O A] [Group H]

/-- Use the original residue-field identification and the original whole residual identity
to pull the specified residual model back to the actual maximal-ideal quotient representation. -/
def originalResidualHopfModel
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (τ : H →* GeneralLinearGroup ι A)
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eA).toRingHom).comp τ = σ)
    (j : (K ≃ₐ[F] K) →* H)
    (m : FiniteFreeHopfPointModel.{u,u,u,u,u} R F K
      (Multiplicative (ι → IsLocalRing.ResidueField O))
      (matrixUnderlyingGroupAction (σ.comp j))) :
    FiniteFreeHopfPointModel.{u,u,u,u,u} R F K
      (Multiplicative (ι → A ⧸ IsLocalRing.maximalIdeal A))
      (matrixUnderlyingGroupAction
        (matrixIdealQuotientRepresentation (IsLocalRing.maximalIdeal A) (τ.comp j))) := by
  have hres : (GeneralLinearGroup.map eA.toRingHom).comp
      (matrixIdealQuotientRepresentation (IsLocalRing.maximalIdeal A) (τ.comp j)) =
      σ.comp j := by
    apply MonoidHom.ext
    intro g
    exact DFunLike.congr_fun hτ (j g)
  apply matrixCoefficientHopfModelOfInjective eA.toRingHom eA.injective
  rw [hres]
  exact m

/-- The original residual identity supplies a genuine model at the original maximal ideal,
from the specified residual representation's model, without assuming the target model. -/
theorem originalResidualHopfModel_exists
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (τ : H →* GeneralLinearGroup ι A)
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eA).toRingHom).comp τ = σ)
    (j : (K ≃ₐ[F] K) →* H)
    (m : FiniteFreeHopfPointModel.{u,u,u,u,u} R F K
      (Multiplicative (ι → IsLocalRing.ResidueField O))
      (matrixUnderlyingGroupAction (σ.comp j))) :
    Nonempty (FiniteFreeHopfPointModel.{u,u,u,u,u} R F K
      (Multiplicative (ι → A ⧸ IsLocalRing.maximalIdeal A))
      (matrixUnderlyingGroupAction
        (matrixIdealQuotientRepresentation (IsLocalRing.maximalIdeal A) (τ.comp j)))) := by
  exact ⟨originalResidualHopfModel eA τ σ hτ j m⟩

end
end Dubon2026
