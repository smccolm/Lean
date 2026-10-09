import Dubon2026.CompletedCoefficientMaximalIdeal

/-! # The actual framed representation fiber of the original residual completion -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι O A : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [CommRing A] [IsLocalRing A] [Algebra O A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]

/-- Actual maps from the original completed coordinate ring preserving its literal residual point. -/
abbrev CompletedCoefficientCoordinateFiber
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O) :=
  { f : ResidualRepresentationCompletion ρ →ₐ[O] A //
    (localCoefficientReduction e).comp f = completedResidualRepresentationEvaluation ρ }

/-- Evaluating the original completed universal representation gives an actual lift of the entire residual representation. -/
def completedRepresentationFromCoordinates
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : CompletedCoefficientCoordinateFiber ρ e) :
    MatrixRepresentationFiber ρ (localCoefficientReduction e) := by
  refine ⟨(GeneralLinearGroup.map (n := ι) (R := ResidualRepresentationCompletion ρ)
    (S := A) f.val.toRingHom).comp (completedUniversalMatrixRepresentation ρ), ?_⟩
  apply MonoidHom.ext
  intro g
  apply Units.ext
  apply Matrix.ext
  intro i j
  change localCoefficientReduction e (f.val ((completedUniversalMatrixRepresentation ρ g).val i j)) =
    (ρ g).val i j
  have hf : localCoefficientReduction e (f.val ((completedUniversalMatrixRepresentation ρ g).val i j)) =
      completedResidualRepresentationEvaluation ρ ((completedUniversalMatrixRepresentation ρ g).val i j) :=
    DFunLike.congr_fun f.property _
  rw [hf]
  exact congrArg (fun u : GeneralLinearGroup ι (IsLocalRing.ResidueField O) => u.val i j)
    (DFunLike.congr_fun (completedUniversalMatrixRepresentation_reduction ρ) g)

/-- The actual completed coordinate fiber is equivalent to the original whole matrix representation fiber. -/
def completedCoefficientRepresentationEquiv
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O) :
    CompletedCoefficientCoordinateFiber ρ e ≃ MatrixRepresentationFiber ρ (localCoefficientReduction e) where
  toFun := completedRepresentationFromCoordinates ρ e
  invFun τ := ⟨completedLocalCoefficientCoordinateMap ρ e
      ((representationCoordinateFiberEquiv ρ (localCoefficientReduction e)).symm τ),
    completedLocalCoefficientCoordinateMap_reduction ρ e _⟩
  left_inv f := by
    apply Subtype.ext
    exact completedLocalCoefficientCoordinateMap_unique ρ e
      (completedRepresentationFromCoordinates ρ e f) f.val rfl
  right_inv τ := by
    apply Subtype.ext
    exact completedLocalCoefficientCoordinateMap_representation ρ e τ

/-- The completed-fiber equivalence evaluates the entire original completed universal representation. -/
theorem completedCoefficientRepresentationEquiv_evaluation
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (τ : MatrixRepresentationFiber ρ (localCoefficientReduction e)) :
    (GeneralLinearGroup.map (n := ι) (R := ResidualRepresentationCompletion ρ) (S := A)
      ((completedCoefficientRepresentationEquiv ρ e).symm τ).val.toRingHom).comp
        (completedUniversalMatrixRepresentation ρ) = τ.val :=
  completedLocalCoefficientCoordinateMap_representation ρ e τ

end
end Dubon2026
