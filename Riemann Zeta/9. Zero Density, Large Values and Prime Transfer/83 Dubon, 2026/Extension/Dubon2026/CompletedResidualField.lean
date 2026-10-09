import Dubon2026.CompletedResidualLocalRing

/-! # The actual residue field of the genuine original residual completion -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι O : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]

/-- The true residue field of the original completed local ring is canonically identified with the original coefficient residue field. -/
def completedResidualFieldEquiv
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    IsLocalRing.ResidueField (ResidualRepresentationCompletion ρ) ≃ₐ[O]
      IsLocalRing.ResidueField O :=
  (Ideal.quotientEquivAlgOfEq O (completedResidualRepresentationEvaluation_ker ρ).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (completedResidualRepresentationEvaluation_surjective ρ))

/-- The actual completed residue-field identification sends the literal residue of every original completed element to its genuine residual evaluation. -/
theorem completedResidualFieldEquiv_residue
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (x : ResidualRepresentationCompletion ρ) :
    completedResidualFieldEquiv ρ (IsLocalRing.residue _ x) =
      completedResidualRepresentationEvaluation ρ x := rfl

/-- Through the true residue field of the original completion, the entire completed universal representation still reduces to the original residual representation. -/
theorem completedUniversalMatrixRepresentation_trueResidue
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    (GeneralLinearGroup.map (n := ι) (R := ResidualRepresentationCompletion ρ)
      (S := IsLocalRing.ResidueField O) ((completedResidualFieldEquiv ρ).toRingHom.comp
      (IsLocalRing.residue (ResidualRepresentationCompletion ρ)))).comp
        (completedUniversalMatrixRepresentation ρ) = ρ := by
  have h : (completedResidualFieldEquiv ρ).toRingHom.comp
      (IsLocalRing.residue (ResidualRepresentationCompletion ρ)) =
      (completedResidualRepresentationEvaluation ρ).toRingHom := by
    ext x
    exact completedResidualFieldEquiv_residue ρ x
  rw [h]
  exact completedUniversalMatrixRepresentation_reduction ρ

end
end Dubon2026
