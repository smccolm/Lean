import Dubon2026.MatrixHopfModelCoefficientIdealLocal
import Dubon2026.OriginalAdicLocalQuotientData

/-! # The genuine model coefficient quotient in its original complete local topology -/

namespace Dubon2026
noncomputable section
open Matrix
universe u

variable {R F K A ι : Type u} [CommRing R] [Field F] [Field K]
  [Algebra R F] [Algebra F K] [Algebra R K] [IsScalarTower R F K]
  [CommRing A] [IsLocalRing A] [TopologicalSpace A] [IsTopologicalRing A] [Fintype ι] [DecidableEq ι]

/-- The original maximal-adic topology makes the actual maximal ideal open. A genuine
model of the same residual representation therefore makes the original model quotient local. -/
theorem matrixHopfModelCoefficientQuotient_isLocal_of_isAdic
    (hA : IsAdic (IsLocalRing.maximalIdeal A))
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A)
    (m : FiniteFreeHopfPointModel.{u,u,u,u,u} R F K
      (Multiplicative (ι → A ⧸ IsLocalRing.maximalIdeal A))
      (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation (IsLocalRing.maximalIdeal A) ρ))) :
    IsLocalRing (A ⧸ matrixHopfModelCoefficientIdeal R F K ρ) := by
  apply matrixHopfModelCoefficientQuotient_isLocal ρ _ m
  simpa using (isAdic_iff.mp hA).1 1

variable [IsNoetherianRing A] [Finite (IsLocalRing.ResidueField A)]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]

/-- The literal model coefficient quotient is Noetherian, complete and maximal-adic in its
actual quotient topology. Its locality is derived from the original residual model. -/
theorem matrixHopfModelCoefficientQuotient_localData
    (hA : IsAdic (IsLocalRing.maximalIdeal A))
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A)
    (m : FiniteFreeHopfPointModel.{u,u,u,u,u} R F K
      (Multiplicative (ι → A ⧸ IsLocalRing.maximalIdeal A))
      (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation (IsLocalRing.maximalIdeal A) ρ))) :
    let J := matrixHopfModelCoefficientIdeal R F K ρ
    letI := matrixHopfModelCoefficientQuotient_isLocal_of_isAdic hA ρ m
    IsNoetherianRing (A ⧸ J) ∧ IsAdic (IsLocalRing.maximalIdeal (A ⧸ J)) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal (A ⧸ J)) (A ⧸ J) := by
  letI := matrixHopfModelCoefficientQuotient_isLocal_of_isAdic hA ρ m
  exact originalAdicLocalQuotient_localData hA (matrixHopfModelCoefficientIdeal R F K ρ)

end
end Dubon2026
