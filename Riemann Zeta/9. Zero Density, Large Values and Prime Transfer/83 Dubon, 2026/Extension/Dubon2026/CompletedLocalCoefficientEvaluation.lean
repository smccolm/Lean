import Dubon2026.CompletedResidualRepresentation
import Dubon2026.LocalCoefficientRepresentationFibers
import Dubon2026.AdicCoefficientCompletionMaps

/-! # Actual original representation evaluation over complete local coefficient algebras -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι O A : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [CommRing A] [IsLocalRing A] [Algebra O A]

/-- The actual original local coefficient lift carries the genuine residual ideal into the true coefficient maximal ideal. -/
theorem localizedCoefficientCoordinateMap_ideal
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : RepresentationCoordinateFiber ρ (localCoefficientReduction e)) :
    RingHom.ker (localizedResidualRepresentationEvaluation ρ).toRingHom ≤
      Ideal.comap (localizedCoefficientCoordinateMap ρ e f).toRingHom
        (IsLocalRing.maximalIdeal A) := by
  intro x hx
  apply (localCoefficientReduction_eq_zero_iff e _).mp
  have h := DFunLike.congr_fun (localizedCoefficientCoordinateMap_reduction ρ e f) x
  exact h.trans hx

/-- For a genuine complete local coefficient target, the actual original coordinate lift extends to its real residual completion. -/
def completedLocalCoefficientCoordinateMap [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : RepresentationCoordinateFiber ρ (localCoefficientReduction e)) :
    ResidualRepresentationCompletion ρ →ₐ[O] A := by
  let completedMap := adicCompleteCoefficientMap (O := O)
    (R := ResidualRepresentationLocalRing ρ) (A := A)
    (RingHom.ker (R := ResidualRepresentationLocalRing ρ)
      (S := IsLocalRing.ResidueField O) (localizedResidualRepresentationEvaluation ρ).toRingHom)
    (IsLocalRing.maximalIdeal A) (localizedCoefficientCoordinateMap ρ e f)
    (localizedCoefficientCoordinateMap_ideal ρ e f)
  exact completedMap

/-- The genuine complete-target coordinate map agrees with the actual original localized lift on every original element. -/
theorem completedLocalCoefficientCoordinateMap_of
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : RepresentationCoordinateFiber ρ (localCoefficientReduction e))
    (x : ResidualRepresentationLocalRing ρ) :
    completedLocalCoefficientCoordinateMap ρ e f
      (algebraMap _ (ResidualRepresentationCompletion ρ) x) =
        localizedCoefficientCoordinateMap ρ e f x := by
  let evaluation := adicCompleteCoefficientMap_of (O := O)
    (R := ResidualRepresentationLocalRing ρ) (A := A)
    (RingHom.ker (R := ResidualRepresentationLocalRing ρ)
      (S := IsLocalRing.ResidueField O) (localizedResidualRepresentationEvaluation ρ).toRingHom)
    (IsLocalRing.maximalIdeal A) (localizedCoefficientCoordinateMap ρ e f)
    (localizedCoefficientCoordinateMap_ideal ρ e f) x
  exact evaluation

/-- Evaluating the entire genuine completed universal representation recovers the original matrix representation over the actual complete local coefficient algebra. -/
theorem completedLocalCoefficientCoordinateMap_representation
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (τ : MatrixRepresentationFiber ρ (localCoefficientReduction e)) :
    (GeneralLinearGroup.map (n := ι) (R := ResidualRepresentationCompletion ρ) (S := A)
      (completedLocalCoefficientCoordinateMap ρ e
      ((representationCoordinateFiberEquiv ρ (localCoefficientReduction e)).symm τ)).toRingHom).comp
        (completedUniversalMatrixRepresentation ρ) = τ.val := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  apply Matrix.ext
  intro i j
  change completedLocalCoefficientCoordinateMap ρ e
    ((representationCoordinateFiberEquiv ρ (localCoefficientReduction e)).symm τ)
    (algebraMap _ (ResidualRepresentationCompletion ρ)
      ((localizedUniversalMatrixRepresentation ρ g).val i j)) = (τ.val g).val i j
  rw [completedLocalCoefficientCoordinateMap_of]
  exact congrArg (fun u : GeneralLinearGroup ι A => u.val i j)
    (DFunLike.congr_fun (localizedCoefficientCoordinateMap_representation ρ e τ) g)

end
end Dubon2026
