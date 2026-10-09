import Dubon2026.RepresentationCoordinateEvaluation
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # The actual residual point of matrix coordinates over an original local coefficient ring -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι O : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]

/-- The original residual representation evaluates the coordinate algebra over the genuine local coefficient ring surjectively onto its actual residue field. -/
theorem residualRepresentationCoordinateEvaluation_surjective
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    Function.Surjective (representationCoordinateEvaluation (R := O) ρ) := by
  intro x
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (R := O) x
  refine ⟨algebraMap O (RepresentationCoordinateAlgebra G ι O) a, ?_⟩
  rw [AlgHom.commutes, IsLocalRing.ResidueField.algebraMap_eq]
  exact ha

/-- The literal kernel of the original residual point on the coordinate algebra over the original local coefficient ring. -/
def residualRepresentationCoordinateIdeal
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    Ideal (RepresentationCoordinateAlgebra G ι O) :=
  RingHom.ker (representationCoordinateEvaluation (R := O) ρ).toRingHom

/-- The actual original residual point is a genuine maximal ideal of the coordinate algebra over the local coefficient ring. -/
theorem residualRepresentationCoordinateIdeal_isMaximal
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    (residualRepresentationCoordinateIdeal ρ).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (representationCoordinateEvaluation (R := O) ρ).toRingHom
    (residualRepresentationCoordinateEvaluation_surjective ρ)

/-- The original residual-point quotient is the genuine residue field of the original local coefficient ring, as an algebra over that ring. -/
def residualRepresentationCoordinateQuotientEquiv
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    (RepresentationCoordinateAlgebra G ι O ⧸ residualRepresentationCoordinateIdeal ρ) ≃ₐ[O]
      IsLocalRing.ResidueField O :=
  Ideal.quotientKerAlgEquivOfSurjective (residualRepresentationCoordinateEvaluation_surjective ρ)

/-- The original residual point quotient is exactly evaluated by the original residual representation. -/
theorem residualRepresentationCoordinateQuotientEquiv_mk
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (x : RepresentationCoordinateAlgebra G ι O) :
    residualRepresentationCoordinateQuotientEquiv ρ
      (Ideal.Quotient.mk (residualRepresentationCoordinateIdeal ρ) x) =
        representationCoordinateEvaluation (R := O) ρ x := rfl

end
end Dubon2026
