import Dubon2026.MatrixOpenIdealHopfModelFromClosedFamily
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # The actual closed coefficient ideal determined by original open quotient models

The defining family uses the given original representation. The equivalence below
derives its open-quotient classification from compactness and genuine model
closure. It does not assert an initial arithmetic model or a universal deformation.
-/

namespace Dubon2026
noncomputable section
open Matrix
universe u

variable (R F K : Type u) {A ι : Type u} [CommRing R] [Field F] [Field K]
  [Algebra R F] [Algebra F K] [Algebra R K] [IsScalarTower R F K]
  [CommRing A] [TopologicalSpace A] [Fintype ι] [DecidableEq ι]

/-- The actual open ideals whose original quotient representations have genuine finite free integral Hopf models. Membership is a condition, not an existence assertion. -/
def matrixHopfModelIdealFamily (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A) :
    Set (Ideal A) :=
  {I | IsOpen (I : Set A) ∧
    Nonempty (FiniteFreeHopfPointModel.{u,u,u,u,u} R F K (Multiplicative (ι → A ⧸ I))
      (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation I ρ)))}

/-- The literal intersection of the actual original open model ideals. -/
def matrixHopfModelCoefficientIdeal (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A) : Ideal A :=
  ⨅ I : {I : Ideal A // I ∈ matrixHopfModelIdealFamily R F K ρ}, I.val

variable {R F K} [IsTopologicalRing A]

/-- The model coefficient ideal is genuinely closed in the original coefficient topology: every original open additive ideal is closed, and the literal ideal intersection is the corresponding set intersection. -/
theorem matrixHopfModelCoefficientIdeal_isClosed
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A) :
    IsClosed (matrixHopfModelCoefficientIdeal R F K ρ : Set A) := by
  have heq : (matrixHopfModelCoefficientIdeal R F K ρ : Set A) =
      ⋂ I : {I : Ideal A // I ∈ matrixHopfModelIdealFamily R F K ρ}, (I.val : Set A) := by
    ext x
    simp only [matrixHopfModelCoefficientIdeal, SetLike.mem_coe, Ideal.mem_iInf, Set.mem_iInter]
  rw [heq]
  exact isClosed_iInter fun I => I.val.toAddSubgroup.isClosed_of_isOpen I.property.1

variable [IsDomain R] [IsPrincipalIdealRing R] [PerfectField F] [IsFractionRing R F]
  [Normal F K] [IsAlgClosed K] [CompactSpace A]

/-- An original open quotient admits a model exactly when its ideal contains the actual closed model coefficient ideal. One existing original open quotient model supplies a nonempty family; compactness and the genuine finite intersection constructions derive every other model in the forward direction. -/
theorem matrixHopfModelCoefficientIdeal_le_iff
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A)
    (I₀ : Ideal A) (hI₀ : IsOpen (I₀ : Set A))
    (m₀ : FiniteFreeHopfPointModel.{u,u,u,u,u} R F K (Multiplicative (ι → A ⧸ I₀))
      (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation I₀ ρ)))
    (U : Ideal A) (hU : IsOpen (U : Set A)) :
    matrixHopfModelCoefficientIdeal R F K ρ ≤ U ↔
      Nonempty (FiniteFreeHopfPointModel.{u,u,u,u,u} R F K (Multiplicative (ι → A ⧸ U))
        (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation U ρ))) := by
  constructor
  · intro hsub
    exact matrixOpenIdealHopfModel_of_closedFamily
      (fun I : {I : Ideal A // I ∈ matrixHopfModelIdealFamily R F K ρ} => I.val)
      (fun I => I.val.toAddSubgroup.isClosed_of_isOpen I.property.1)
      ⟨I₀, hI₀, ⟨m₀⟩⟩ ρ (fun I => I.property.2) U hU hsub
  · intro hmodel
    exact iInf_le (fun I : {I : Ideal A // I ∈ matrixHopfModelIdealFamily R F K ρ} => I.val)
      ⟨U, hU, hmodel⟩

end
end Dubon2026
