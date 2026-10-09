import Dubon2026.FirstOrderCohomologyClassification
import Dubon2026.ContinuousFirstOrderDeformation
import Dubon2026.SymmetricRepresentationReduction

/-! # Actual symmetric powers of original first-order lifts and strict conjugacies -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G R : Type} [Group G] [CommRing R]

/-- The genuine symmetric power of an original dual-number lift reduces to the original symmetric-power representation. -/
def symmetricFirstOrderLift (n : ℕ) (ρ : G →* GeneralLinearGroup (Fin 2) R)
    (τ : MatrixFirstOrderLift ρ) : MatrixFirstOrderLift (symmetricMatrixRepresentation n ρ) := by
  refine ⟨symmetricMatrixRepresentation n τ.val, ?_⟩
  change (GeneralLinearGroup.map (TrivSqZeroExt.fstHom R R R).toRingHom).comp
    (symmetricMatrixRepresentation n τ.val) = symmetricMatrixRepresentation n ρ
  rw [symmetricMatrixRepresentation_map]
  exact congrArg (symmetricMatrixRepresentation n) τ.property

/-- The actual strict change of basis on the original rank-two lift gives the genuine symmetric-power strict change of basis. -/
theorem symmetricFirstOrderLift_strictlyConjugate (n : ℕ)
    (ρ : G →* GeneralLinearGroup (Fin 2) R) (τ σ : MatrixFirstOrderLift ρ)
    (h : MatrixFirstOrderStrictlyConjugate ρ τ σ) :
    MatrixFirstOrderStrictlyConjugate (symmetricMatrixRepresentation n ρ)
      (symmetricFirstOrderLift n ρ τ) (symmetricFirstOrderLift n ρ σ) := by
  obtain ⟨U, hU, hc⟩ := h
  refine ⟨homogeneousSymmetricGL n U, ?_, ?_⟩
  · change GeneralLinearGroup.map (TrivSqZeroExt.fstHom R R R).toRingHom
      (homogeneousSymmetricGL n U) = 1
    rw [homogeneousSymmetricGL_map]
    change homogeneousSymmetricGL n (dualMatrixReduction U) = 1
    rw [hU, map_one]
  · intro g
    exact symmetricMatrixRepresentation_conjugate n τ.val σ.val U hc g

/-- Equality of original first-order adjoint classes is preserved by the actual symmetric-power construction on their genuine lifts. -/
theorem symmetricFirstOrderLift_cohomology (n : ℕ)
    (ρ : G →* GeneralLinearGroup (Fin 2) R) (τ σ : MatrixFirstOrderLift ρ)
    (h : groupCohomology.H1π (matrixAdjointRep ρ) (matrixFirstOrderCocycle ρ τ) =
      groupCohomology.H1π (matrixAdjointRep ρ) (matrixFirstOrderCocycle ρ σ)) :
    groupCohomology.H1π (matrixAdjointRep (symmetricMatrixRepresentation n ρ))
      (matrixFirstOrderCocycle _ (symmetricFirstOrderLift n ρ τ)) =
        groupCohomology.H1π (matrixAdjointRep (symmetricMatrixRepresentation n ρ))
          (matrixFirstOrderCocycle _ (symmetricFirstOrderLift n ρ σ)) :=
  (matrixFirstOrderStrictlyConjugate_iff _ _ _).mp
    (symmetricFirstOrderLift_strictlyConjugate n ρ τ σ
      ((matrixFirstOrderStrictlyConjugate_iff ρ τ σ).mpr h))

/-- The actual symmetric-power first-order lift retains continuity in the original dual-number topology. -/
theorem symmetricFirstOrderLift_continuous [TopologicalSpace G]
    [TopologicalSpace R] [IsTopologicalRing R] (n : ℕ)
    (ρ : G →* GeneralLinearGroup (Fin 2) R) (τ : MatrixFirstOrderLift ρ)
    (hτ : Continuous τ.val) : Continuous (symmetricFirstOrderLift n ρ τ).val :=
  symmetricMatrixRepresentation_continuous n τ.val hτ

end
end Dubon2026
