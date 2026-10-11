import Dubon2026.MatrixFiniteIdealIntersectionHopfModels
import Dubon2026.CompactClosedIdealFiniteIntersection

/-! # Actual open quotient models from compact closed families of original models -/

namespace Dubon2026
noncomputable section
open Matrix
universe u

variable {R F K A ι η : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [CommRing A] [TopologicalSpace A] [CompactSpace A] [Fintype ι] [DecidableEq ι]

/-- An actual compact closed family of original quotient models supplies a model modulo each original open ideal containing its intersection. Compactness extracts a finite nonempty family; its genuine product-subgroup model and the original quotient transition construct the required model. -/
theorem matrixOpenIdealHopfModel_of_closedFamily
    (I : η → Ideal A) (hI : ∀ i, IsClosed (I i : Set A)) (i₀ : η)
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A)
    (hmodels : ∀ i,
      Nonempty (FiniteFreeHopfPointModel.{u,u,u,u,u} R F K (Multiplicative (ι → A ⧸ I i))
        (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation (I i) ρ))))
    (U : Ideal A) (hU : IsOpen (U : Set A)) (hsub : (⨅ i, I i) ≤ U) :
    Nonempty (FiniteFreeHopfPointModel.{u,u,u,u,u} R F K (Multiplicative (ι → A ⧸ U))
      (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation U ρ))) := by
  obtain ⟨s, hi₀, hs⟩ := compactClosedIdeals_finiteIntersection_le I hI U hU hsub i₀
  obtain ⟨m⟩ := matrixFiniteIdealIntersectionHopfModel_exists I s ⟨i₀, hi₀⟩ ρ
    (fun i _hi => hmodels i)
  exact matrixIdealQuotientHopfModel_transition_exists (⨅ i ∈ s, I i) U hs ρ m

end
end Dubon2026
