import Dubon2026.LocalizedResidualEvaluation
import Mathlib.RingTheory.AdicCompletion.Completeness

/-! # The actual adic completion of the original residual representation local ring -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι O : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]

/-- The literal adic completion of the original residual localization at its genuine residual kernel. -/
abbrev ResidualRepresentationCompletion
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :=
  AdicCompletion (R := ResidualRepresentationLocalRing ρ)
    (RingHom.ker (R := ResidualRepresentationLocalRing ρ)
    (S := IsLocalRing.ResidueField O) (localizedResidualRepresentationEvaluation ρ).toRingHom)
    (ResidualRepresentationLocalRing ρ)

/-- The original residual local ring acts on its genuine completion through the canonical adic algebra map. -/
instance residualRepresentationCompletionAlgebra
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    Algebra (ResidualRepresentationLocalRing ρ) (ResidualRepresentationCompletion ρ) := by
  letI : Algebra (ResidualRepresentationLocalRing ρ) (ResidualRepresentationLocalRing ρ) :=
    Algebra.id (ResidualRepresentationLocalRing ρ)
  let algebraStructure := AdicCompletion.instAlgebra (R := ResidualRepresentationLocalRing ρ)
    (S := ResidualRepresentationLocalRing ρ)
    (RingHom.ker (R := ResidualRepresentationLocalRing ρ)
      (S := IsLocalRing.ResidueField O) (localizedResidualRepresentationEvaluation ρ).toRingHom)
  exact algebraStructure

/-- The actual completed residual point obtained from the original surjective residual evaluation. -/
def completedResidualRepresentationEvaluation
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    ResidualRepresentationCompletion ρ →ₐ[O] IsLocalRing.ResidueField O := by
  let projection := AdicCompletion.kerProj (R := O) (S := ResidualRepresentationLocalRing ρ)
    (A := IsLocalRing.ResidueField O) (f := localizedResidualRepresentationEvaluation ρ)
    (localizedResidualRepresentationEvaluation_surjective ρ)
  exact projection

/-- The genuine completed residual point agrees with the original residual evaluation on every original local element. -/
theorem completedResidualRepresentationEvaluation_of
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (x : ResidualRepresentationLocalRing ρ) :
    completedResidualRepresentationEvaluation ρ
      (algebraMap _ (ResidualRepresentationCompletion ρ) x) =
        localizedResidualRepresentationEvaluation ρ x := rfl

/-- The actual completed residual point is onto the original coefficient residue field. -/
theorem completedResidualRepresentationEvaluation_surjective
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    Function.Surjective (completedResidualRepresentationEvaluation ρ) := by
  let surjectivity := AdicCompletion.kerProj_surjective (R := O)
    (S := ResidualRepresentationLocalRing ρ)
    (A := IsLocalRing.ResidueField O) (f := localizedResidualRepresentationEvaluation ρ)
    (localizedResidualRepresentationEvaluation_surjective ρ)
  exact surjectivity

/-- The entire original universal matrix representation with coefficients in its genuine residual completion. -/
def completedUniversalMatrixRepresentation
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    G →* GeneralLinearGroup ι (ResidualRepresentationCompletion ρ) := by
  let coefficientMap : ResidualRepresentationLocalRing ρ →+*
      ResidualRepresentationCompletion ρ := algebraMap _ _
  let matrixMap : GeneralLinearGroup ι (ResidualRepresentationLocalRing ρ) →*
      GeneralLinearGroup ι (ResidualRepresentationCompletion ρ) :=
    GeneralLinearGroup.map (n := ι) (R := ResidualRepresentationLocalRing ρ)
      (S := ResidualRepresentationCompletion ρ) coefficientMap
  exact matrixMap.comp (localizedUniversalMatrixRepresentation ρ)

/-- The genuine completed universal representation reduces to the entire original residual representation. -/
theorem completedUniversalMatrixRepresentation_reduction
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    (GeneralLinearGroup.map (n := ι) (R := ResidualRepresentationCompletion ρ)
      (S := IsLocalRing.ResidueField O) (completedResidualRepresentationEvaluation ρ).toRingHom).comp
      (completedUniversalMatrixRepresentation ρ) = ρ := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  apply Matrix.ext
  intro i j
  change completedResidualRepresentationEvaluation ρ
    (algebraMap _ (ResidualRepresentationCompletion ρ)
      ((localizedUniversalMatrixRepresentation ρ g).val i j)) = (ρ g).val i j
  rw [completedResidualRepresentationEvaluation_of]
  exact congrArg (fun u : GeneralLinearGroup ι (IsLocalRing.ResidueField O) => u.val i j)
    (DFunLike.congr_fun (localizedUniversalMatrixRepresentation_reduction ρ) g)

/-- Under abstract finite generation and a Noetherian coefficient ring, the actual residual completion is complete for its original residual ideal action. -/
theorem residualRepresentationCompletion_isAdicComplete [Group.FG G] [IsNoetherianRing O]
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    IsAdicComplete (R := ResidualRepresentationLocalRing ρ)
      (RingHom.ker (R := ResidualRepresentationLocalRing ρ)
      (S := IsLocalRing.ResidueField O) (localizedResidualRepresentationEvaluation ρ).toRingHom)
      (ResidualRepresentationCompletion ρ) := by
  letI := residualRepresentationLocalRing_isNoetherian ρ
  exact AdicCompletion.isAdicComplete (M := ResidualRepresentationLocalRing ρ)
    ((isNoetherianRing_iff_ideal_fg _).mp inferInstance _)

end
end Dubon2026
